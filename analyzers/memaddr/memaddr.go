// Package memaddr checks that rules which combine, fold, or forward memory
// operations keep their addresses consistent.
package memaddr

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/memchain/mem"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "memaddr",
	Doc: `report rules whose memory ops' addresses don't match what they replace

A memory op's address is its pointer argument plus its [offset] and {sym}.
Rules that combine, fold, or forward memory ops must carry all three
consistently. memaddr reports:

  - Unconstrained addresses in combines. In a match, an omitted [off] or
    {sym} matches anything, so a rule combining two or more memory ops
    must bind or pin each one's offset and symbol. Without [0] {s},
        (MOVBstore [7] p1 (SHRQconst [56] w) ... x3:(MOVBstore p1 w mem)) => (MOVQstore p1 w mem)
    merges stores at any offsets into one at offset 0. Ops on pointers
    related by isSamePtr or sequentialAddresses count as combined.
  - Dropped offsets and symbols. A result memory op with the same pointer
    and memory as a matched one must carry that op's offset and symbol,
    unless the condition pins them to 0 and nil:
        (ORW (MOVBQZXload [i] {s} p mem) ...) => (MOVWload p mem)
    loads from p+0 instead of s+p+i. Likewise, a rule folding address
    arithmetic into a memory op must keep both offsets (and symbols):
        (MOVQload [off1] {sym} (ADDQconst [off2] ptr) mem) => (MOVQload [off2] {sym} ptr mem)
    drops off1.
  - Symbols on computed bases. A {sym} names its own base (SB, SP, or the
    pointer it was matched with); a result (MOVWload [i] {s} (ADDQ p idx) mem)
    misassembles when s is a stack slot.
  - The wrong end of sequential addresses. sequentialAddresses(a, b, n)
    says a is the lower address, so the combined op must use a;
    likewise i1 == i0+n, or a match with [i] outside and [i-8] inside,
    makes the lower one the combined op's offset.
  - Store forwarding without matching addresses. A rule that replaces a
    load by a value stored in its memory chain must prove the load reads
    what that store wrote: the same pointer (isSamePtr), offset, and
    symbol, as in
        (MOVQload [off] {sym} ptr (MOVQstore [off2] {sym2} ptr2 x _)) && sym == sym2 && off == off2 && isSamePtr(ptr, ptr2) => x
    A generic rule replacing (Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 x _)))
    by x must compare p1 with p3 and t1's size with t3's, not t2's
    (unless t1.Compare(x.Type) == types.CMPeq already makes them equal).
  - Read-modify-write fusion of different locations. A store of an op on
    a load fused into a modify op must load from the address it stores
    to, at the memory state it stores over.
  - Reads through stores without a disjointness proof. A rule that
    takes a load's value from below a store, as in
        (Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 x _))) && isSamePtr(p1, p3) => x
    must prove (with Disjoint) that each store it reads past doesn't
    overlap the loaded location.
  - Reads of volatile memory moved later. A generic rule that reads a
    Move's source again, (Move dst tmp m:(Move tmp src _)) => (Move dst src m),
    must check !isVolatile(src): the outgoing argument area that src may
    point to is clobbered by calls inserted after the rule runs.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	t := mem.Ops(pass.Corpus)
	for r := range pass.Rules() {
		if r.IsBlock() || r.Result == nil {
			continue
		}
		mr := mem.Analyze(t, r)
		checkUnconstrained(pass, mr)
		checkDropped(pass, mr)
		checkFolded(pass, mr)
		checkComputedBase(pass, mr)
		checkSequential(pass, mr)
		checkMatchedOrder(pass, mr)
		checkForwarding(pass, mr)
		checkRMW(pass, mr)
		checkVolatile(pass, mr)
		checkDisjoint(pass, mr)
	}
	return nil
}

// addressed reports whether v is a memory op with an [offset] or {sym}.
func addressed(r *mem.Rule, v *rules.Value) bool {
	return !v.IsLeaf() && r.Info(v).Mem && strings.HasPrefix(v.Op.Aux, "Sym")
}

// free reports whether s, a match's [auxint] or {aux}, matches anything.
func free(s string) bool { return s == "" || s == "_" }

// combine returns, for a rule whose result is a single memory op with a
// variable pointer, that op and the matched memory ops on the same
// location: those whose pointer is the result's, or is related to it by
// isSamePtr, sequentialAddresses, or ==. It returns nil if there are fewer
// than two.
func combine(r *mem.Rule) (res *rules.Value, ops []*rules.Value) {
	res = r.Result
	if !addressed(r, res) {
		return nil, nil
	}
	p := leafArg(res, mem.PtrArg(res.Op))
	if p == "" {
		return nil, nil
	}
	group := map[string]bool{p: true}
	var pairs [][2]string
	for _, fn := range []string{"isSamePtr", "sequentialAddresses"} {
		for _, call := range r.Cond.Calls[fn] {
			pairs = append(pairs, [2]string{mem.ArgIdent(call, 0), mem.ArgIdent(call, 1)})
		}
	}
	for changed := true; changed; {
		changed = false
		for _, pp := range pairs {
			if pp[0] != "" && pp[1] != "" && group[pp[0]] != group[pp[1]] {
				group[pp[0]], group[pp[1]] = true, true
				changed = true
			}
		}
	}
	r.Match.Walk(func(v *rules.Value) bool {
		if !addressed(r, v) {
			return true
		}
		q := leafArg(v, mem.PtrArg(v.Op))
		for g := range group {
			if q != "" && r.Cond.SameValue(q, g) {
				ops = append(ops, v)
				break
			}
		}
		return true
	})
	if len(ops) < 2 {
		return nil, nil
	}
	return res, ops
}

// checkUnconstrained reports combines in which a matched op's [offset]
// or {sym} matches anything.
func checkUnconstrained(pass *analysis.Pass, r *mem.Rule) {
	_, ops := combine(r)
	for _, v := range ops {
		var missing []string
		if v.Op.HasAuxInt && free(v.AuxInt) {
			missing = append(missing, "[offset]")
		}
		if v.Op.HasAux && free(v.Aux) {
			missing = append(missing, "{sym}")
		}
		if len(missing) > 0 {
			pass.Reportf(r.Pos, "%s is combined with other memory ops but its %s %s unconstrained: an omitted [offset] or {sym} matches any value, not 0 or nil",
				opDesc(v), strings.Join(missing, " and "), map[bool]string{true: "are", false: "is"}[len(missing) > 1])
		}
	}
}

func opDesc(v *rules.Value) string {
	if v.Name != "" {
		return fmt.Sprintf("%s (%s)", v.Name, v.OpName)
	}
	return v.OpName
}

// pinned reports whether the condition has a conjunct name == lit.
func pinned(r *mem.Rule, name, lit string) bool {
	for _, c := range r.Cond.Conjuncts {
		b, ok := c.(*ast.BinaryExpr)
		if !ok || b.Op != token.EQL {
			continue
		}
		x, y := exprText(b.X), exprText(b.Y)
		if x == name && y == lit || y == name && x == lit {
			return true
		}
	}
	return false
}

func exprText(e ast.Expr) string {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		return e.Name
	case *ast.BasicLit:
		return e.Value
	}
	return ""
}

// leafArg returns the name of v's argument i if it is a variable, or "".
func leafArg(v *rules.Value, i int) string {
	if i < len(v.Args) && v.Args[i].IsVar() {
		return v.Args[i].Name
	}
	return ""
}

// checkDropped reports result memory ops that access the same pointer as
// matched memory ops but carry none of their offsets (or symbols). A combine carries one of several: (ORW x0:(MOVBload [i0] {s} p mem)
// ... x1:(MOVBload [i1] {s} p mem)) && i1 == i0+1 => (MOVWload [i0] {s} p mem).
func checkDropped(pass *analysis.Pass, r *mem.Rule) {
	r.Result.Walk(func(res *rules.Value) bool {
		if !addressed(r, res) {
			return !res.IsLeaf()
		}
		p := leafArg(res, mem.PtrArg(res.Op))
		if p == "" {
			return true
		}
		var like *rules.Value
		var offs, syms []string
		r.Match.Walk(func(v *rules.Value) bool {
			if !addressed(r, v) || leafArg(v, mem.PtrArg(v.Op)) != p {
				return true
			}
			if like == nil {
				like = v
			}
			if rules.IsVarText(v.AuxInt) && !pinned(r, v.AuxInt, "0") {
				offs = append(offs, v.AuxInt)
			}
			if rules.IsVarText(v.Aux) && !pinned(r, v.Aux, "nil") {
				syms = append(syms, v.Aux)
			}
			return true
		})
		if len(offs) > 0 && !mentionsAny(res.AuxInt, offs) {
			pass.Reportf(r.Pos, "%s accesses %s like %s, but drops its offset %s: the result accesses a different address unless %s == 0",
				res.OpName, p, opDesc(like), offs[0], offs[0])
		}
		if len(syms) > 0 && !mentionsAny(res.Aux, syms) {
			pass.Reportf(r.Pos, "%s accesses %s like %s, but drops its symbol %s: the result accesses a different address unless %s == nil",
				res.OpName, p, opDesc(like), syms[0], syms[0])
		}
		return true
	})
}

// checkFolded checks address-folding rules, which fold the address
// arithmetic computing a memory op's pointer into the op:
//
//	(MOVQload [off1] {sym} (ADDQconst [off2] ptr) mem) => (MOVQload [off1+off2] {sym} ptr mem)
//
// The result must carry the offsets and symbols of both the op and the
// folded arithmetic, unless the condition pins them to 0 and nil.
func checkFolded(pass *analysis.Pass, r *mem.Rule) {
	root, res := r.Match, r.Result
	if !addressed(r, root) || !addressed(r, res) {
		return
	}
	q := root.Args[mem.PtrArg(root.Op)]
	p := leafArg(res, mem.PtrArg(res.Op))
	if q.IsLeaf() || p == "" {
		return
	}
	inQ := false
	for _, a := range q.Args {
		if a.IsVar() && a.Name == p {
			inQ = true
		}
	}
	if !inQ {
		return
	}
	for _, v := range []*rules.Value{root, q} {
		if rules.IsVarText(v.AuxInt) && !pinned(r, v.AuxInt, "0") && !mentionsAny(res.AuxInt, []string{v.AuxInt}) {
			pass.Reportf(r.Pos, "%s folds %s into its address but drops %s's offset %s: the result accesses a different address unless %s == 0",
				res.OpName, q.OpName, opDesc(v), v.AuxInt, v.AuxInt)
		}
		if v.Op.HasAux && strings.HasPrefix(v.Op.Aux, "Sym") && rules.IsVarText(v.Aux) && !pinned(r, v.Aux, "nil") && !mentionsAny(res.Aux, []string{v.Aux}) {
			pass.Reportf(r.Pos, "%s folds %s into its address but drops %s's symbol %s: the result accesses a different address unless %s == nil",
				res.OpName, q.OpName, opDesc(v), v.Aux, v.Aux)
		}
	}
}

func mentionsAny(expr string, names []string) bool {
	ids := mem.Idents(expr)
	for _, n := range names {
		if ids[n] {
			return true
		}
	}
	return false
}

// symVars returns the match's {sym} variables of addressed ops, mapped
// to the op that binds each.
func symVars(r *mem.Rule) map[string]*rules.Value {
	syms := make(map[string]*rules.Value)
	r.Match.Walk(func(v *rules.Value) bool {
		if !v.IsLeaf() && v.Op.HasAux && strings.HasPrefix(v.Op.Aux, "Sym") && rules.IsVarText(v.Aux) && syms[v.Aux] == nil {
			syms[v.Aux] = v
		}
		return true
	})
	return syms
}

// checkComputedBase reports result memory ops that carry a matched {sym}
// on a base pointer computed by ordinary arithmetic.
func checkComputedBase(pass *analysis.Pass, r *mem.Rule) {
	syms := symVars(r)
	if len(syms) == 0 {
		return
	}
	r.Result.Walk(func(res *rules.Value) bool {
		if res.IsLeaf() {
			return false
		}
		if !r.Info(res).Mem || !strings.HasPrefix(res.Op.Aux, "Sym") {
			return true
		}
		var sym string
		for s := range mem.Idents(res.Aux) {
			if syms[s] != nil {
				sym = s
			}
		}
		i := mem.PtrArg(res.Op)
		if sym == "" || i >= len(res.Args) {
			return true
		}
		base := res.Args[i]
		if base.IsLeaf() || base.Op.IsGeneric() || base.Op.SymEffect == "Addr" || base.Op.HasAux {
			// Generic address arithmetic (OffPtr, AddPtr) is lowered
			// to ops that the address-folding rules fold into the
			// access, back onto the symbol's base.
			return true
		}
		pass.Reportf(r.Pos, "%s carries symbol %s on a computed base (%s): a symbol is relative to its own base (SB, SP, or the pointer matched with it), so this addresses the wrong memory when %s is a global or stack symbol",
			res.OpName, sym, base.OpName, sym)
		return true
	})
}

// checkSequential checks rules whose condition orders two addresses or
// offsets: the combined op must start at the lower one.
func checkSequential(pass *analysis.Pass, r *mem.Rule) {
	for _, call := range r.Cond.Calls["sequentialAddresses"] {
		lo, hi := mem.ArgIdent(call, 0), mem.ArgIdent(call, 1)
		if lo == "" || hi == "" {
			continue
		}
		r.Result.Walk(func(res *rules.Value) bool {
			if res.IsLeaf() || !r.Info(res).Mem {
				return !res.IsLeaf()
			}
			if p := leafArg(res, mem.PtrArg(res.Op)); p == hi {
				pass.Reportf(r.Pos, "%s uses %s, but sequentialAddresses(%s, %s, ...) makes %s the higher address; the combined access must start at %s",
					res.OpName, hi, lo, hi, hi, lo)
			}
			return true
		})
	}
	// hi == lo+n: the result's offset must mention lo, not hi.
	offs := make(map[string]bool)
	r.Match.Walk(func(v *rules.Value) bool {
		if addressed(r, v) && rules.IsVarText(v.AuxInt) {
			offs[v.AuxInt] = true
		}
		return true
	})
	for _, c := range r.Cond.Conjuncts {
		hi, lo, ok := offsetOrder(c)
		if !ok || !offs[hi] || !offs[lo] {
			continue
		}
		r.Result.Walk(func(res *rules.Value) bool {
			if res.IsLeaf() || !r.Info(res).Mem {
				return !res.IsLeaf()
			}
			ids := mem.Idents(res.AuxInt)
			if ids[hi] && !ids[lo] {
				pass.Reportf(r.Pos, "%s uses offset %s, but the condition makes %s the higher offset (%s); the combined access must start at %s",
					res.OpName, hi, hi, exprString(c), lo)
			}
			return true
		})
	}
}

// checkMatchedOrder checks combines whose match orders the offsets
// itself, as in
//
//	(MOVDstore [i] {s} ptr x x2:(MOVDstore [i-8] {s} ptr y mem)) => (STP [i-8] {s} ptr y x mem)
//
// where [i-8] compares the inner store's offset with i-8: the combined op
// must start at the lowest of the offsets.
func checkMatchedOrder(pass *analysis.Pass, r *mem.Rule) {
	res, ops := combine(r)
	if res == nil || !res.Op.HasAuxInt {
		return
	}
	base, d, ok := offsetExpr(res.AuxInt)
	if !ok {
		return
	}
	var low *rules.Value
	lowD := d
	for _, v := range ops {
		if b, vd, ok := offsetExpr(v.AuxInt); ok && b == base && vd < lowD {
			low, lowD = v, vd
		}
	}
	if low == nil {
		return
	}
	pass.Reportf(r.Pos, "%s uses offset [%s], but the match puts %s at [%s], a lower offset; the combined access must start at the lowest one",
		res.OpName, res.AuxInt, opDesc(low), low.AuxInt)
}

// offsetExpr parses an [auxint] of the form i, i+n, or i-n, with i an
// identifier and n an integer literal, into i and the signed n.
func offsetExpr(s string) (base string, delta int64, ok bool) {
	if s == "" {
		return "", 0, false
	}
	e, err := parser.ParseExpr(s)
	if err != nil {
		return "", 0, false
	}
	if id, ok := e.(*ast.Ident); ok && rules.IsVarText(id.Name) {
		return id.Name, 0, true
	}
	b, ok := e.(*ast.BinaryExpr)
	if !ok || b.Op != token.ADD && b.Op != token.SUB {
		return "", 0, false
	}
	id, ok := b.X.(*ast.Ident)
	lit, ok2 := b.Y.(*ast.BasicLit)
	if !ok || !ok2 || lit.Kind != token.INT {
		return "", 0, false
	}
	n, err := strconv.ParseInt(lit.Value, 0, 64)
	if err != nil {
		return "", 0, false
	}
	if b.Op == token.SUB {
		n = -n
	}
	return id.Name, n, true
}

func exprString(e ast.Expr) string {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		return e.Name
	case *ast.BasicLit:
		return e.Value
	case *ast.BinaryExpr:
		return exprString(e.X) + " " + e.Op.String() + " " + exprString(e.Y)
	}
	return "..."
}

// offsetOrder recognizes hi == lo+n (or lo+n == hi) with n a positive
// integer literal.
func offsetOrder(c ast.Expr) (hi, lo string, ok bool) {
	b, isBin := c.(*ast.BinaryExpr)
	if !isBin || b.Op != token.EQL {
		return "", "", false
	}
	try := func(x, y ast.Expr) (string, string, bool) {
		h := exprText(x)
		sum, ok := ast.Unparen(y).(*ast.BinaryExpr)
		if h == "" || !ok || sum.Op != token.ADD {
			return "", "", false
		}
		l := exprText(sum.X)
		lit, ok := ast.Unparen(sum.Y).(*ast.BasicLit)
		if !ok || lit.Kind != token.INT {
			return "", "", false
		}
		if n, err := strconv.Atoi(lit.Value); err != nil || n <= 0 || !token.IsIdentifier(l) || !token.IsIdentifier(h) {
			return "", "", false
		}
		return h, l, true
	}
	if h, l, ok := try(b.X, b.Y); ok {
		return h, l, true
	}
	return try(b.Y, b.X)
}

// checkForwarding checks store-to-load forwarding rules: a load whose
// result is built from the value of a store in its memory chain, without
// reading memory, must prove that it reads the location that store wrote:
// the same pointer (by name, x == y, or isSamePtr), the same other address
// arguments, offset, and symbol, and, for a generic Load, the same size.
func checkForwarding(pass *analysis.Pass, r *mem.Rule) {
	root := r.Match
	if ri := r.Info(root); ri.Out != mem.OutNone || !ri.Mem || !ri.Read {
		return
	}
	reads := false
	r.Result.Walk(func(v *rules.Value) bool {
		if r.MemArg(v) != nil {
			reads = true
		}
		return !reads && !v.IsLeaf()
	})
	if reads {
		return
	}
	// The stores in the load's memory chain, and the one whose value the
	// result uses.
	var stores []*rules.Value
	for s := r.MemArg(root); s != nil && !s.IsLeaf() && len(s.Args) >= 2; s = r.MemArg(s) {
		if si := r.Info(s); si.Out != mem.OutMem || si.Read {
			break
		}
		stores = append(stores, s)
	}
	var src *rules.Value
	var x string
	for _, s := range stores {
		if n := storedName(s); n != "" && mem.Mentions(r.Result, n) {
			src, x = s, n
			break
		}
	}
	if src == nil {
		return
	}
	la := root.Args[mem.PtrArg(root.Op) : len(root.Args)-1]
	sa := src.Args[:len(src.Args)-2]
	if len(la) != len(sa) || len(la) == 0 {
		return
	}
	for i := range la {
		if !la[i].IsVar() || !sa[i].IsVar() {
			return
		}
	}
	lp, sp := la[0].Name, sa[0].Name
	if !samePtr(r, lp, sp) {
		// Name a wrong isSamePtr partner if there is one.
		why := fmt.Sprintf("nothing establishes isSamePtr(%s, %s)", lp, sp)
		for _, call := range r.Cond.Calls["isSamePtr"] {
			a, b := mem.ArgIdent(call, 0), mem.ArgIdent(call, 1)
			if b == lp {
				a, b = b, a
			}
			if a == lp && b != "" {
				why = fmt.Sprintf("the condition compares %s with %s instead", lp, b)
				for _, s := range stores {
					if s != src && leafArg(s, 0) == b {
						why += ", another store's pointer"
					}
				}
			}
		}
		pass.Reportf(r.Pos, "the result uses %s, stored by %s to %s, but %s: the %s from %s may read a different location",
			x, src.OpName, sp, why, root.OpName, lp)
	}
	for i := 1; i < len(la); i++ {
		if !sameValue(r, la[i].Name, sa[i].Name) {
			pass.Reportf(r.Pos, "the result uses %s, stored by %s, but the %s's address argument %s isn't shown equal to the store's %s: it may read a different location",
				x, src.OpName, root.OpName, la[i].Name, sa[i].Name)
		}
	}
	if root.Op.HasAuxInt && src.Op.HasAuxInt && !sameValue(r, root.AuxInt, src.AuxInt) {
		pass.Reportf(r.Pos, "the result uses %s, stored by %s at [%s], but the %s's [%s] isn't shown equal to it: it may read a different offset",
			x, src.OpName, src.AuxInt, root.OpName, root.AuxInt)
	}
	if addressed(r, root) && addressed(r, src) && root.Op.HasAux && src.Op.HasAux && !sameValue(r, root.Aux, src.Aux) {
		pass.Reportf(r.Pos, "the result uses %s, stored by %s with {%s}, but the %s's {%s} isn't shown equal to it: it may read a different symbol",
			x, src.OpName, src.Aux, root.OpName, root.Aux)
	}
	checkForwardedSize(pass, r, root, src, stores, x)
}

// storedName returns the variable naming the value that store s writes:
// its value argument, or the [auxint] of a constant value argument, as in
// (Store {t2} p2 (Const64 [x]) _).
func storedName(s *rules.Value) string {
	v := s.Args[len(s.Args)-2]
	switch {
	case v.IsVar():
		return v.Name
	case !v.IsLeaf() && len(v.Args) == 0 && rules.IsVarText(v.AuxInt):
		return v.AuxInt
	}
	return ""
}

// samePtr reports whether pointers a and b are the same by name, x == y,
// or a chain of isSamePtr conjuncts.
func samePtr(r *mem.Rule, a, b string) bool {
	same := map[string]bool{a: true}
	for changed := true; changed; {
		changed = false
		for _, call := range r.Cond.Calls["isSamePtr"] {
			x, y := mem.ArgIdent(call, 0), mem.ArgIdent(call, 1)
			if x == "" || y == "" || same[x] == same[y] {
				continue
			}
			same[x], same[y] = true, true
			changed = true
		}
	}
	for n := range same {
		if r.Cond.SameValue(n, b) {
			return true
		}
	}
	return false
}

// sameValue reports whether match expressions a and b are equal: the same
// text, or related by an a == b conjunct.
func sameValue(r *mem.Rule, a, b string) bool {
	if strings.TrimSpace(a) == strings.TrimSpace(b) {
		return true
	}
	return pinned(r, a, b) || r.Cond.SameValue(a, b)
}

// checkForwardedSize checks that a generic Load forwarding the value of
// Store src compares its size with src's type. A conjunct making the
// load's type identical to the forwarded value's (t1.Compare(x.Type) ==
// types.CMPeq) proves it, and makes any size comparison redundant.
func checkForwardedSize(pass *analysis.Pass, r *mem.Rule, root, src *rules.Value, stores []*rules.Value, x string) {
	if !root.Op.IsGeneric() || root.Op.Name != "Load" || !r.Result.IsVar() {
		return
	}
	t1, tK := root.Type, src.Aux
	if typesIdentical(r, t1, x) {
		return
	}
	typOf := map[string]bool{}
	for _, s := range stores {
		if s != src {
			typOf[s.Aux] = true
		}
	}
	for _, c := range r.Cond.Conjuncts {
		a, b, ok := sizeEq(c)
		if !ok {
			continue
		}
		other := ""
		switch t1 {
		case a:
			other = b
		case b:
			other = a
		}
		if other != "" && other != tK && typOf[other] {
			pass.Reportf(r.Pos, "the result is %s, stored with type %s, but the condition compares the load's size with %s.Size(), another store's type, not %s.Size(): a value of a different size could be forwarded", x, tK, other, tK)
		}
	}
}

// typesIdentical reports whether the condition has t.Compare(x.Type) ==
// types.CMPeq (in either order).
func typesIdentical(r *mem.Rule, t, x string) bool {
	for _, c := range r.Cond.Conjuncts {
		b, ok := c.(*ast.BinaryExpr)
		if !ok || b.Op != token.EQL {
			continue
		}
		call, ok := ast.Unparen(b.X).(*ast.CallExpr)
		if !ok {
			continue
		}
		if sel, ok := ast.Unparen(b.Y).(*ast.SelectorExpr); !ok || sel.Sel.Name != "CMPeq" {
			continue
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "Compare" || len(call.Args) != 1 {
			continue
		}
		recv, arg := typeName(sel.X), typeName(call.Args[0])
		if recv == t && arg == x || recv == x && arg == t {
			return true
		}
	}
	return false
}

// typeName returns t for an identifier t and x for x.Type.
func typeName(e ast.Expr) string {
	switch e := ast.Unparen(e).(type) {
	case *ast.Ident:
		return e.Name
	case *ast.SelectorExpr:
		if id, ok := e.X.(*ast.Ident); ok && e.Sel.Name == "Type" {
			return id.Name
		}
	}
	return ""
}

// sizeEq recognizes a.Size() == b.Size().
func sizeEq(c ast.Expr) (a, b string, ok bool) {
	e, isBin := c.(*ast.BinaryExpr)
	if !isBin || e.Op != token.EQL {
		return "", "", false
	}
	size := func(x ast.Expr) string {
		call, ok := ast.Unparen(x).(*ast.CallExpr)
		if !ok || len(call.Args) != 0 {
			return ""
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "Size" {
			return ""
		}
		return exprText(sel.X)
	}
	a, b = size(e.X), size(e.Y)
	return a, b, a != "" && b != ""
}

// checkRMW checks rules that fuse a store of an op on a load into a
// read-modify-write op: the load must read the location stored to.
func checkRMW(pass *analysis.Pass, r *mem.Rule) {
	root, res := r.Match, r.Result
	if res.IsLeaf() || res.Op.IsGeneric() || res.Op.SymEffect != "Read,Write" {
		return
	}
	ri := r.Info(root)
	if ri.Out != mem.OutMem || ri.Read || !addressed(r, root) {
		return
	}
	m := r.MemArg(root)
	if m == nil || !m.IsVar() {
		return
	}
	pi := mem.PtrArg(root.Op)
	ptr := leafArg(root, pi)
	if ptr == "" {
		return
	}
	var bad []string
	for i, a := range root.Args {
		if i == pi || a == m {
			continue
		}
		a.Walk(func(l *rules.Value) bool {
			if !addressed(r, l) || r.Info(l).Out != mem.OutNone {
				return true
			}
			lm := r.MemArg(l)
			if lm == nil {
				return true
			}
			lp := leafArg(l, mem.PtrArg(l.Op))
			switch {
			case !lm.IsVar() || !r.Cond.SameValue(lm.Name, m.Name):
				bad = append(bad, fmt.Sprintf("reads memory state %s, not %s, the state the store writes over", lm.Text, m.Name))
			case lp == "" || !samePtr(r, lp, ptr):
				bad = append(bad, fmt.Sprintf("loads from %s, not %s", l.Args[mem.PtrArg(l.Op)].Text, ptr))
			case !sameValue(r, l.AuxInt, root.AuxInt):
				bad = append(bad, fmt.Sprintf("loads at offset [%s], not [%s]", l.AuxInt, root.AuxInt))
			case !sameValue(r, l.Aux, root.Aux):
				bad = append(bad, fmt.Sprintf("loads symbol {%s}, not {%s}", l.Aux, root.Aux))
			}
			return true
		})
	}
	for _, b := range bad {
		pass.Reportf(r.Pos, "%s is fused into read-modify-write %s, but its load %s: the fused op reads exactly the location it writes, at the memory state it writes over", root.OpName, res.OpName, b)
	}
}

// checkVolatile checks generic rules that read a Move's source anew.
func checkVolatile(pass *analysis.Pass, r *mem.Rule) {
	if !r.Set.Arch.Generic {
		return
	}
	// Pointers that the match reads as a Move's source, before the root.
	// (A result that reads the root's own source reads it at the same
	// point in the program.)
	srcs := make(map[string]bool)
	r.Match.Walk(func(v *rules.Value) bool {
		if v != r.Match && !v.IsLeaf() && v.Op.IsGeneric() && v.Op.Name == "Move" {
			if p := leafArg(v, 1); p != "" {
				srcs[p] = true
			}
		}
		return true
	})
	if root := r.Match; root.Op.IsGeneric() {
		switch root.Op.Name {
		case "Load":
			delete(srcs, leafArg(root, 0))
		case "Move":
			delete(srcs, leafArg(root, 1))
		}
	}
	if len(srcs) == 0 {
		return
	}
	var notVolatile = make(map[string]bool)
	for _, call := range r.Cond.NotCalls["isVolatile"] {
		notVolatile[mem.ArgIdent(call, 0)] = true
	}
	reported := make(map[string]bool)
	r.Result.Walk(func(v *rules.Value) bool {
		if v.IsLeaf() || !v.Op.IsGeneric() {
			return !v.IsLeaf()
		}
		var p string
		switch v.Op.Name {
		case "Load":
			p = leafArg(v, 0)
		case "Move":
			p = leafArg(v, 1)
		}
		if p != "" && srcs[p] && !notVolatile[p] && !reported[p] {
			reported[p] = true
			pass.Reportf(r.Pos, "the result reads %s, a matched Move's source, in a new %s without checking !isVolatile(%s): if %s points into the outgoing argument area, calls inserted later (such as typedmemmove for write barriers) clobber it before the read",
				p, v.Op.Name, p, p)
		}
		return true
	})
}

// checkDisjoint checks generic rules that read a location's contents
// through stores in the root's memory chain: forwarding a stored value to
// a load, loading from a Zero below stores, or eliminating a store of a
// value just loaded. Each store between the root and the state the rule
// reads from must be proven disjoint from the root's address.
func checkDisjoint(pass *analysis.Pass, r *mem.Rule) {
	root := r.Match
	if !root.Op.IsGeneric() || (root.Op.Name != "Load" && root.Op.Name != "Store") || len(root.Args) < 2 {
		return
	}
	// Rules that write again (Move from stores) re-issue what they skip.
	writes := false
	r.Result.Walk(func(v *rules.Value) bool {
		if !v.IsLeaf() && r.Info(v).Out == mem.OutMem {
			writes = true
		}
		return !writes
	})
	if writes {
		return
	}
	// The root's memory chain of generic writers.
	var chain []*rules.Value
	depth := make(map[string]int) // memory variable -> chain index of the state it names
	for c := root.Args[len(root.Args)-1]; ; c = c.Args[len(c.Args)-1] {
		if c.Name != "" {
			depth[c.Name] = len(chain)
		}
		if c.IsLeaf() || !c.Op.IsGeneric() || r.Info(c).Out != mem.OutMem || len(c.Args) == 0 {
			break
		}
		chain = append(chain, c)
	}
	if len(chain) == 0 {
		return
	}
	// The names denoting the root's address, closed under isSamePtr.
	same := make(map[string]bool)
	for n := range names(root.Args[0]) {
		same[n] = true
	}
	ptrPairs := [][2]string{}
	for _, call := range r.Cond.Calls["isSamePtr"] {
		ptrPairs = append(ptrPairs, [2]string{mem.ArgIdent(call, 0), mem.ArgIdent(call, 1)})
	}
	for changed := true; changed; {
		changed = false
		for _, pp := range ptrPairs {
			if same[pp[0]] != same[pp[1]] && pp[0] != "" && pp[1] != "" {
				same[pp[0]], same[pp[1]] = true, true
				changed = true
			}
		}
	}
	// The deepest chain state the rule reads the root's location from.
	k := 0
	for i, c := range chain {
		switch {
		case c.Op.Name == "Store" && r.Result.IsVar() && leafArg(c, 1) == r.Result.Name:
			k = max(k, i) // forwards c's value
		case len(c.Args) > 0 && overlaps(names(c.Args[0]), same) && i > 0:
			k = max(k, i) // reads c's contents (a Zero, or a Store of a constant)
		}
	}
	if root.Op.Name == "Store" {
		if ld := root.Args[1]; !ld.IsLeaf() && ld.Op.Name == "Load" && len(ld.Args) == 2 && overlaps(names(ld.Args[0]), same) {
			if d, ok := depth[ld.Args[1].Name]; ok {
				k = max(k, d) // stores back a value loaded from below
			}
		}
	}
	for _, w := range chain[:k] {
		if w.Op.ZeroWidth || len(w.Args) == 0 {
			continue
		}
		wp := names(w.Args[0])
		if len(wp) == 0 || disjointProven(r, wp, same) {
			continue
		}
		what := w.Args[0].Text
		if a := w.Args[0]; a.Name != "" {
			what = a.Name
		}
		pass.Reportf(r.Pos, "the rule assumes the %s to %s doesn't change the root's location, but the condition doesn't establish that with Disjoint: if they overlap, the rule uses a stale value",
			w.OpName, what)
	}
}

// names returns the variables naming address expression v: its binding
// name and the variables in it.
func names(v *rules.Value) map[string]bool {
	ns := make(map[string]bool)
	v.Walk(func(w *rules.Value) bool {
		if rules.IsVarText(w.Name) {
			ns[w.Name] = true
		}
		return true
	})
	return ns
}

func overlaps(a, b map[string]bool) bool {
	for n := range a {
		if b[n] {
			return true
		}
	}
	return false
}

// disjointProven reports whether a Disjoint or Disjoint1 conjunct
// relates one of wp to one of same.
func disjointProven(r *mem.Rule, wp, same map[string]bool) bool {
	for _, fn := range []string{"disjoint", "disjoint1"} {
		for _, call := range r.Cond.Calls[fn] {
			var ids []map[string]bool
			for i := range call.Args {
				ids = append(ids, mem.ArgIdents(call, i))
			}
			for i := range ids {
				for j := range ids {
					if i != j && overlaps(ids[i], wp) && overlaps(ids[j], same) {
						return true
					}
				}
			}
		}
	}
	return false
}
