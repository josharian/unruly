// Package memchain checks that rules keep the memory chain well formed:
// that values a rule bypasses, re-issues, or clobbers are provably dead.
package memchain

import (
	"fmt"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/memchain/mem"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "memchain",
	Doc: `report rules that can leave two memory states or two loads live

A rewrite rule replaces only the value it matched (the root). Everything
else it matched stays in the function, with all of its other uses, unless
the condition proves it has none (x.Uses == 1, or CanMergeLoad, which
checks it). memchain reports rules whose soundness depends on such a value
being dead without the condition proving it:

  - Re-issued loads. A rule that folds a matched load into a new memory
    op, such as
        (Bswap16 x:(MOVHZload [off] {sym} ptr mem)) => (MOVHBRload [off] {sym} ptr mem)
    turns one read of memory into two if x has another use: x itself
    remains for that use. A racing write can then make the two copies of
    one Go-level load disagree (see test/atomicload.go). Every match node
    between the root and x must die too, or it keeps x live:
        (ORL x0:(MOVBload [i] {s} p mem) s0:(SHLLconst [8] x1:(MOVBload [i+1] {s} p mem)))
    needs s0.Uses == 1 as well as x0.Uses == 1 and x1.Uses == 1.
  - Re-read Move sources. A Move stays for the uses of its memory state,
    so a rule that reads its source again, such as
        (Load <t1> p1 move:(Move [n] p2 src mem)) && isSamePtr(p1, p2) => @move.Block (Load <t1> src mem)
    turns one copy of *src into two reads unless src is on the stack
    (isStackPtr(src)), where no other goroutine can write it.
  - Bypassed memory producers. A rule whose result uses a memory state
    from below a matched store or call, such as
        (SelectN [1] call:(StaticLECall ...  mem)) && clobberIfDead(call) => mem
    leaves the skipped op live alongside the older memory if the op has
    other uses: two memory states are live at once, which is invalid SSA
    (or the op's side effect is lost for those uses).
  - Clobber without a use count. Clobber(x) resets x to OpInvalid; if x
    has uses outside the match, they are left pointing at an invalid value.
  - Side effects under a selector. A rule rooted at (Select0 t) or
    (Select1 t) that creates a new memory op from t's arguments duplicates
    t's side effect if a sibling selector of t is rewritten the same way;
    t.Uses == 1 rules that out.

A use count proves a value dead if it is at most the number of places the
match refers to the value (counting x == y aliases). One structural idiom
needs no use count: a rule rooted at (SelectN [0] call) whose result is a
memory state shows that the call has no results, so the root is the
call's only use.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	t := mem.Ops(pass.Corpus)
	for r := range pass.Rules() {
		if r.IsBlock() || r.Result == nil {
			continue
		}
		mr := mem.Analyze(t, r)
		checkReissue(pass, mr)
		checkBypass(pass, mr)
		checkClobber(pass, mr)
		checkSelector(pass, mr)
	}
	return nil
}

// describe names match node v for a diagnostic, such as "x (MOVHZload)".
func describe(v *rules.Value) string {
	if v.Name != "" {
		return fmt.Sprintf("%s (%s)", v.Name, v.OpName)
	}
	return v.OpName
}

// checkReissue reports rules whose result reads again, through a new
// memory op, what a matched op has already read, without proving that the
// matched op dies: a load re-issued at its own memory and address, or a
// Move's source read again.
func checkReissue(pass *analysis.Pass, r *mem.Rule) {
	r.Match.Walk(func(l *rules.Value) bool {
		if l == r.Match || l.IsLeaf() {
			return true
		}
		info := r.Info(l)
		m := r.MemArg(l)
		if !info.Mem || m == nil {
			return true
		}
		switch {
		case info.Out == mem.OutNone && m.IsVar():
			if !aggregate(r) {
				checkReissuedLoad(pass, r, l, m)
			}
		case isMove(l):
			checkRereadMove(pass, r, l)
		}
		return true
	})
}

// checkReissuedLoad checks a matched load l with memory argument m.
func checkReissuedLoad(pass *analysis.Pass, r *mem.Rule, l, m *rules.Value) {
	addr := map[string]bool{}
	for _, a := range l.Args[:len(l.Args)-1] {
		if a.IsVar() {
			addr[a.Name] = true
		}
	}
	reissued := reader(r, addr, func(nm *rules.Value) bool { return nm.Name == m.Name })
	if reissued == nil {
		return
	}
	if l.Name == "" || !r.Dies(l.Name) {
		what := "nothing proves it has no other uses"
		if l.Name != "" {
			what = fmt.Sprintf("the condition doesn't establish %s.Uses == %d", l.Name, max(r.Refs(l.Name), 1))
		}
		pass.Reportf(r.Pos, "load %s is re-issued as %s, but %s: if it has another use, one load becomes two, which can observe different values",
			describe(l), reissued.OpName, what)
		return
	}
	// l dies only if every match node between it and the root does:
	// a live intermediate keeps l live.
	for p := r.Parent[l]; p != nil && p != r.Match; p = r.Parent[p] {
		if p.Name != "" && r.Dies(p.Name) {
			continue
		}
		what := fmt.Sprintf("%s is unnamed, so the condition can't establish that it has no other uses", p.OpName)
		if p.Name != "" {
			what = fmt.Sprintf("the condition doesn't establish %s.Uses == %d", p.Name, max(r.Refs(p.Name), 1))
		}
		pass.Reportf(r.Pos, "load %s is re-issued as %s from under %s, but %s: if %s has another use, it keeps %s live, and one load becomes two, which can observe different values",
			describe(l), reissued.OpName, describe(p), what, describe(p), l.Name)
	}
}

// checkRereadMove checks a matched Move mv whose source the result may
// read again.
func checkRereadMove(pass *analysis.Pass, r *mem.Rule, mv *rules.Value) {
	src := mv.Args[1]
	if !src.IsVar() {
		return
	}
	if mv.Name != "" && r.Dies(mv.Name) {
		return
	}
	for _, call := range r.Cond.Calls["isStackPtr"] {
		if mem.ArgIdent(call, 0) == src.Name {
			// Stack memory can't change under a racing goroutine.
			return
		}
	}
	reread := reader(r, map[string]bool{src.Name: true}, func(nm *rules.Value) bool { return r.MemVars[nm.Name] })
	if reread == nil {
		return
	}
	pass.Reportf(r.Pos, "the result reads %s, the source of %s, again in a new %s, but the condition doesn't establish isStackPtr(%s): the Move stays for its other uses, so one copy from *%s becomes two reads, which can observe different values",
		src.Name, describe(mv), reread.OpName, src.Name, src.Name)
}

// isMove reports whether v is a generic Move, (Move dst src mem).
func isMove(v *rules.Value) bool {
	return !v.IsLeaf() && v.Op.IsGeneric() && v.Op.Name == "Move" && len(v.Args) == 3
}

// reader returns the first memory-reading node of r's result whose memory
// argument is a variable satisfying memOK and whose other arguments
// mention one of addr, or nil.
func reader(r *mem.Rule, addr map[string]bool, memOK func(*rules.Value) bool) *rules.Value {
	var found *rules.Value
	r.Result.Walk(func(n *rules.Value) bool {
		if found != nil || n.IsLeaf() {
			return false
		}
		ni := r.Info(n)
		if nm := r.MemArg(n); nm != nil && (ni.Out == mem.OutNone || ni.Read) {
			if nm.IsVar() && memOK(nm) && mentionsAny(n.Args[:len(n.Args)-1], addr) {
				found = n
			}
		}
		return true
	})
	return found
}

// aggregate reports whether r rewrites loads of non-SSA-able or
// aggregate values, which are always decomposed or turned into Moves
// as a whole: (Store dst (Load src mem) mem) && !CanSSA(t) => (Move ...),
// or (StringLen (Load ptr mem)) => (Load (OffPtr ptr) mem) in dec.rules.
func aggregate(r *mem.Rule) bool {
	if len(r.Cond.NotCalls["canSSA"]) > 0 {
		return true
	}
	switch r.Match.Op.Name {
	case "StructSelect", "ArraySelect":
		// opsig says Any because dec.rules also applies these to
		// pointer-shaped values, but a Load they select from is an
		// aggregate.
		return r.Match.Op.IsGeneric()
	}
	sig, ok := opsig.Lookup(r.Match.Op)
	if !ok || len(sig.Args) == 0 {
		return false
	}
	switch sig.Args[0].Kind {
	case opsig.String, opsig.Slice, opsig.Interface, opsig.Complex, opsig.Struct, opsig.Array:
		return true
	}
	return false
}

func mentionsAny(vs []*rules.Value, names map[string]bool) bool {
	for _, v := range vs {
		for n := range names {
			if mem.Mentions(v, n) {
				return true
			}
		}
	}
	return false
}

// chain returns the match nodes on the memory chain below the root:
// starting from the root's memory argument (or, for a root that selects
// the memory of a tuple or call, from that tuple or call), each memory
// producer and selector of one, down to the first node that is neither.
// depth maps the names bound along the chain, and the variable that ends
// it, to their positions: path[i].Name maps to i, and the end to len(path).
func chain(r *mem.Rule) (path []*rules.Value, depth map[string]int) {
	root := r.Match
	var cur *rules.Value
	switch info := r.Info(root); {
	case info.Producer():
		cur = r.MemArg(root)
	case isSelector(root) && root.Args[0].Op != nil && r.Info(root.Args[0]).Producer() && resultIsMem(r):
		cur = root.Args[0]
	}
	depth = make(map[string]int)
	for cur != nil {
		if cur.IsLeaf() {
			if cur.IsVar() {
				depth[cur.Name] = len(path)
			}
			break
		}
		if cur.Name != "" {
			depth[cur.Name] = len(path)
		}
		switch {
		case r.Info(cur).Producer():
			path = append(path, cur)
			cur = r.MemArg(cur)
		case isSelector(cur) && cur.Args[0].Op != nil && r.Info(cur.Args[0]).Producer():
			path = append(path, cur)
			cur = cur.Args[0]
		default:
			cur = nil
		}
	}
	return path, depth
}

func isSelector(v *rules.Value) bool {
	if v.IsLeaf() || len(v.Args) != 1 {
		return false
	}
	switch v.Op.Name {
	case "Select0", "Select1", "SelectN":
		return v.Op.IsGeneric()
	}
	return false
}

// resultIsMem reports whether r's result is a memory state.
func resultIsMem(r *mem.Rule) bool {
	res := r.Result
	if res.IsLeaf() {
		return r.MemVars[res.Name]
	}
	return r.Info(res).Out == mem.OutMem
}

// resultMemVars returns the match variables that r's result uses as
// memory states.
func resultMemVars(r *mem.Rule) []string {
	var vars []string
	if r.Result.IsLeaf() {
		if r.MemVars[r.Result.Name] {
			vars = append(vars, r.Result.Name)
		}
		return vars
	}
	r.Result.Walk(func(v *rules.Value) bool {
		if v.IsLeaf() {
			return false
		}
		if m := r.MemArg(v); m != nil && m.IsVar() {
			vars = append(vars, m.Name)
		}
		return true
	})
	return vars
}

// voidCall reports whether name is a call that the rule shows has no
// results, so that the root is its only use: the root is
// (SelectN [0] name), and the result is a memory state. (A call with n
// results has its memory at SelectN [n].)
func voidCall(r *mem.Rule, name string) bool {
	root := r.Match
	return root.Op.Name == "SelectN" && root.AuxInt == "0" &&
		len(root.Args) == 1 && root.Args[0].Name == name &&
		root.Args[0].Op != nil && root.Args[0].Op.Call && resultIsMem(r)
}

// checkBypass reports memory producers on the root's memory chain that
// the result skips without the condition proving them dead.
func checkBypass(pass *analysis.Pass, r *mem.Rule) {
	path, depth := chain(r)
	if len(path) == 0 {
		return
	}
	deepest, deepestVar := -1, ""
	for _, u := range resultMemVars(r) {
		if d, ok := depth[u]; ok && d > deepest {
			deepest, deepestVar = d, u
		}
	}
	for i, p := range path[:max(deepest, 0)] {
		if p.Name != "" && (mem.Mentions(r.Result, p.Name) || r.Dies(p.Name) || r.Cond.ResetCopy[p.Name] || voidCall(r, p.Name)) {
			continue
		}
		if p.Op.ZeroWidth && recreated(r, p) {
			// (Store dst (Load src mem) (VarDef {x} mem)) => (Move dst src (VarDef {x} mem))
			// moves a zero-width marker rather than skipping it.
			continue
		}
		if isSelector(p) && i+1 < len(path) && path[i+1] == p.Args[0] {
			// A selector is live if and only if its tuple is;
			// report the tuple.
			continue
		}
		var why, it string
		switch {
		case p.Name == "":
			why, it = "it is unnamed, so the condition can't establish that it has no other uses", "it"
		case r.Cond.Clobber[p.Name] || len(r.Cond.Calls["clobberIfDead"]) > 0:
			why = fmt.Sprintf("the condition doesn't establish %s.Uses == %d (Clobber and ClobberIfDead don't)", p.Name, max(r.Refs(p.Name), 1))
			it = p.Name
		default:
			why = fmt.Sprintf("the condition doesn't establish %s.Uses == %d", p.Name, max(r.Refs(p.Name), 1))
			it = p.Name
		}
		pass.Reportf(r.Pos, "result skips %s, using memory %s from below it, but %s: if %s has another use, it stays live alongside %s, and two memory states are live at once",
			describe(p), deepestVar, why, it, deepestVar)
	}
}

// checkClobber reports Clobber(x) of a matched value x that is not
// proven dead.
func checkClobber(pass *analysis.Pass, r *mem.Rule) {
	for _, call := range r.Cond.Calls["clobber"] {
		for i := range call.Args {
			x := mem.ArgIdent(call, i)
			b := r.Bind[x]
			if x == "" || b == nil || b == r.Match {
				continue
			}
			if r.Dies(x) || r.Cond.ResetCopy[x] || voidCall(r, x) {
				continue
			}
			pass.Reportf(r.Pos, "Clobber(%s) without %s.Uses == %d: if %s has other uses, they are left pointing at an invalid value",
				x, x, max(r.Refs(x), 1), x)
		}
	}
}

// checkSelector reports rules rooted at a selector of a matched memory
// op t that create a new memory op without proving t.Uses == 1.
func checkSelector(pass *analysis.Pass, r *mem.Rule) {
	root := r.Match
	if !isSelector(root) || root.Args[0].IsLeaf() {
		return
	}
	t := root.Args[0]
	if !r.Info(t).Mem {
		return
	}
	if t.Name != "" && (r.Dies(t.Name) || voidCall(r, t.Name)) {
		return
	}
	var created *rules.Value
	r.Result.Walk(func(v *rules.Value) bool {
		if created == nil && !v.IsLeaf() && (r.Info(v).Mem || v.Op.HasSideEffects) {
			created = v
		}
		return created == nil
	})
	if created == nil {
		return
	}
	name := t.Name
	if name == "" {
		name = "it"
	}
	pass.Reportf(r.Pos, "result creates memory op %s from %s, whose other selectors may be rewritten the same way, duplicating its side effect; the condition must establish %s.Uses == 1",
		created.OpName, describe(t), name)
}

// recreated reports whether r's result contains a node with the same op,
// auxint, aux, and arguments as match node p.
func recreated(r *mem.Rule, p *rules.Value) bool {
	found := false
	r.Result.Walk(func(v *rules.Value) bool {
		if found || v.IsLeaf() || v.Op != p.Op || v.AuxInt != p.AuxInt || v.Aux != p.Aux || len(v.Args) != len(p.Args) {
			return !found
		}
		for i, a := range v.Args {
			if a.Text != p.Args[i].Text {
				return true
			}
		}
		found = true
		return false
	})
	return found
}
