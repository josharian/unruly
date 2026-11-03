// Package extelim reports rules that remove a sign or zero extension that
// is not redundant.
package extelim

import (
	"fmt"
	"go/ast"
	"go/parser"
	"regexp"
	"slices"
	"strconv"
	"sync"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "extelim",
	Doc: `report rules that remove a sign or zero extension that is not redundant

Rules such as

	(MOVWZreg x:(MOVWZload _ _)) => x

remove an extension because its argument's register is already extended.
Each relies on a fact about a register's bits: here, that MOVWZload
zero-extends. extelim checks four things.

The fact: the argument's op must establish it for every auxint the
condition allows. PPC64's

	(MOVHZreg (SRWconst [c] x)) && x.Type.Size() <= 16 => (SRWconst [c] x)

is wrong: SRWconst [c] zero-extends only from 32-c bits, and the condition
(in bytes, so always true) does not force c >= 16; uint64(uint16(x>>3))
of 0xffffffff becomes 0x1fffffff. So is (MOVBUreg x) && x.Type.IsBoolean()
=> (MOVDreg x): a type says nothing about the bits above it in a register.

Spills: when the result passes x on as is, x's consumers read its register,
and a spilled x is reloaded by a load chosen by x's type. ARM64's

	(MOVWreg x:(MOVBreg _)) => (MOVDreg x)

is wrong because MOVBreg can have type uint32 (uint32(int8(v)) is a
SignExt8to32 of type uint32), and a uint32 is reloaded with MOVWU:
0xffffffffffffff80 comes back as 0x00000000ffffff80, and int32(u)>>40 is 0,
not -1. The possible types of each op are computed from the rules that
create it.

Phases: x's op must not be rewritten, in the same pass or a later one, into
one that lacks the fact. In one pass, ARM64's (MOVWUreg x:(MOVWUreg _)) =>
(MOVDreg x) and (MOVWUreg x) && v.Type.Size() <= 4 => x can apply in either
order; if the first goes first, the outer extension is lost.

Folds: a rule built from extensions, masks, and constants must compute the
same value on both sides in the bits of its type. (MOVBreg (MOVDconst [c]))
=> (MOVDconst [int64(c)]) forgets to sign-extend, and (ANDconst [c]
(MOVBreg x)) => (ANDconst [c&0xff] x) drops a sign extension that c's
upper bits can see.

Facts come from a table: extending loads and extension ops by mnemonic,
zeroUpperBits attributes, the ops rewrite.go's zeroUpperNBits helpers
accept, and hand-written entries for shifts, masks, and set-on-condition
ops. Rules relying on ops the table does not know are not checked.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	c := &checker{pass: pass, types: map[string]*opTypes{}, problems: map[*rules.Rule]*string{}}
	for _, set := range pass.Sets {
		a := archs[set.Arch.Name]
		if a == nil {
			continue
		}
		for _, r := range set.Rules {
			e, ok := elision(a, r)
			if !ok {
				if msg := checkSemantics(a, c.opTypes(set), r); msg != "" {
					pass.Report(r.Pos, msg)
				}
				continue
			}
			if msg := c.phaseProblem(a, r, e); msg != "" {
				pass.Report(r.Pos, msg)
			}
			if msg := c.problem(a, r); msg != "" {
				pass.Report(r.Pos, msg)
			}
		}
	}
	return nil
}

type checker struct {
	pass     *analysis.Pass
	types    map[string]*opTypes     // by arch
	problems map[*rules.Rule]*string // memoized problem results
}

// opTypes returns the op types for the values that set's rules see.
func (c *checker) opTypes(set *rules.RuleSet) *opTypes {
	ot := c.types[set.Arch.Name]
	if ot == nil {
		ot = newOpTypes(c.pass.Corpus, set.Arch.Name)
		c.types[set.Arch.Name] = ot
	}
	ot.forSet(set)
	return ot
}

// elision reports whether r removes an extension, and which.
func elision(a *archInfo, r *rules.Rule) (ext, bool) {
	if r.IsBlock() || r.Match.Op == nil || r.Result == nil || len(r.Match.Args) != 1 {
		return ext{}, false
	}
	e, ok := a.exts[r.Match.Op.Name]
	if !ok || classify(a, r, r.Match.Args[0]) == other {
		return ext{}, false
	}
	return e, true
}

// problem returns what is wrong with the elision rule r on its own,
// or "".
func (c *checker) problem(a *archInfo, r *rules.Rule) string {
	if p := c.problems[r]; p != nil {
		return *p
	}
	e, _ := elision(a, r)
	msg := checkElision(a, c.opTypes(r.Set), r, e)
	c.problems[r] = &msg
	return msg
}

// resultKind is what an elision rule's result does with the extension's
// argument.
type resultKind int

const (
	other     resultKind = iota
	passes               // x, or a register move of x: x's register is used as is
	recreates            // a new value with x's op, auxint, and args
)

func classify(a *archInfo, r *rules.Rule, arg *rules.Value) resultKind {
	res := r.Result
	if arg.Name == "" || arg.Name == "_" {
		if arg.Op != nil && res.Op == arg.Op && sameNode(res, arg) {
			return recreates
		}
		return other
	}
	if res.IsLeaf() {
		if res.Name == arg.Name {
			return passes
		}
		return other
	}
	if a.moves[res.Op.Name] && len(res.Args) == 1 && res.Args[0].IsLeaf() && res.Args[0].Name == arg.Name {
		return passes
	}
	if arg.Op != nil && res.Op == arg.Op && sameNode(res, arg) {
		return recreates
	}
	return other
}

// sameNode reports whether the result node res computes the same thing as
// the match node m: same op, auxint, aux, and args.
func sameNode(res, m *rules.Value) bool {
	if res.AuxInt != m.AuxInt || res.Aux != m.Aux || len(res.Args) != len(m.Args) || res.Ellipsis || m.Ellipsis || m.Rest {
		return false
	}
	for i, ra := range res.Args {
		ma := m.Args[i]
		switch {
		case ra.IsLeaf() && ra.Name == ma.Name && ma.Name != "_" && ma.Name != "":
		case !ra.IsLeaf() && ra.Text == ma.Text:
		default:
			return false
		}
	}
	return true
}

// A world assigns values to some of a rule's variables.
type world struct {
	env   env
	types map[*rules.Value]ssaType // match nodes with a known type
	// For the result of a rule: the facts of its match's leaf variables,
	// and the match nodes its names are bound to.
	leaf  map[string]fact
	bound map[string]*rules.Value
}

func (w world) typeOf(n *rules.Value) (ssaType, bool) {
	t, ok := w.types[n]
	return t, ok
}

// A dim is a variable to enumerate.
type dim struct {
	names []string     // env names it binds
	node  *rules.Value // the match node whose type it is, for type dims
	vals  []val
}

// checkElision checks that the extension e that r removes is redundant,
// and stays redundant across a spill. It returns a description of the
// problem, or "".
func checkElision(a *archInfo, ot *opTypes, r *rules.Rule, e ext) string {
	arg := r.Match.Args[0]
	kind := classify(a, r, arg)
	if arg.Op == nil {
		if r.CondExpr != nil && callsWith(r.CondExpr, arg.Name) {
			return "" // a helper such as ZeroUpper32Bits(x) vouches for x
		}
	} else if _, src := a.opFact(arg, world{}); src == srcNone {
		return "" // an op whose facts we don't know
	}

	var dims []dim
	// Auxints in the argument's subtree.
	arg.Walk(func(n *rules.Value) bool {
		if n.Op != nil && rules.IsVarText(n.AuxInt) {
			if k, ok := kindNames[n.Op.AuxIntType]; ok {
				dims = append(dims, dim{names: []string{n.AuxInt}, vals: auxDomain(k)})
			}
		}
		return true
	})
	// The argument's type matters to a spill and to the facts of Args.
	if arg.Op != nil && (kind == passes || arg.Op.Name == "Arg") {
		var names []string
		if rules.IsVarText(arg.Name) {
			names = append(names, arg.Name+".Type")
		}
		if rules.IsVarText(arg.Type) {
			names = append(names, arg.Type)
		}
		if ts := ot.narrow(r, ot.ofNode(arg), names...); ts != 0 {
			dims = append(dims, dim{names: names, node: arg, vals: typeVals(ts)})
		}
	}
	if arg.Op == nil && rules.IsVarText(arg.Name) && r.CondExpr != nil && mentions(r.CondExpr, arg.Name+".Type") {
		dims = append(dims, dim{names: []string{arg.Name + ".Type"}, vals: typeVals(allTypes)})
	}
	// The rewritten value's type, if the condition looks at it. Otherwise,
	// assume its consumers use all of it.
	var vdim = -1
	if r.CondExpr != nil {
		names := []string{"v.Type"}
		if rules.IsVarText(r.Match.Type) {
			names = append(names, r.Match.Type)
		}
		for _, n := range names {
			if mentions(r.CondExpr, n) {
				vdim = len(dims)
				ts := ot.ofNode(r.Match)
				if ts == 0 {
					ts = allTypes // no rule creates it: we know nothing
				}
				dims = append(dims, dim{names: names, node: r.Match, vals: typeVals(ts)})
				break
			}
		}
	}

	size := 1
	for _, d := range dims {
		size *= len(d.vals)
	}
	if size > 1<<18 {
		return ""
	}
	idx := make([]int, len(dims))
	for {
		w := world{env: env{}, types: map[*rules.Value]ssaType{}}
		for i, d := range dims {
			v := d.vals[idx[i]]
			for _, n := range d.names {
				w.env[n] = v
			}
			if d.node != nil {
				w.types[d.node] = v.t
			}
		}
		if msg := checkWorld(a, ot, r, e, arg, kind, w, vdim >= 0); msg != "" {
			return msg
		}
		// Next world.
		i := 0
		for ; i < len(dims); i++ {
			idx[i]++
			if idx[i] < len(dims[i].vals) {
				break
			}
			idx[i] = 0
		}
		if i == len(dims) {
			return ""
		}
	}
}

// checkWorld checks r in world w, describing the problem if it is wrong.
func checkWorld(a *archInfo, ot *opTypes, r *rules.Rule, e ext, arg *rules.Value, kind resultKind, w world, vTyped bool) string {
	if r.CondExpr != nil {
		if c := eval(r.CondExpr, w.env); c.k == kBool && !c.b {
			return ""
		}
	}
	if vTyped {
		if t, ok := w.typeOf(r.Match); ok && int(t.size())*8 <= e.w {
			// The result's type is no wider than the extension, so
			// its consumers don't look at the extended bits.
			return ""
		}
	}
	if !a.validAux(arg, w) || !constsFit(arg, w) {
		return ""
	}
	f, src := a.opFact(arg, w)
	ename := r.Match.Op.Name
	if !f.holds(e) {
		if arg.Op == nil {
			return fmt.Sprintf("%s (which %s) removed, but nothing makes %s already %s: the condition constrains only its type",
				ename, e, arg.Name, extended(e))
		}
		x, ex := a.factWitness(f, e)
		return fmt.Sprintf("%s (which %s) removed, but %s is %s%s: a register holding %s passes through where %s would give %s",
			ename, e, nodeDesc(arg), f, worldDesc(arg, w), a.hex(x), ename, a.hex(ex))
	}
	if kind != passes || src != srcExact || arg.Op == nil || arg.Op.IsGeneric() || hasAuxVars(arg) {
		// A fact that depends on an auxint, such as ANDconst [c]'s,
		// constrains the value's range in a way that usually agrees
		// with its type; the type analysis can't see that, so don't
		// check spills of such values.
		return ""
	}
	t, ok := w.typeOf(arg)
	if !ok || t == tBool || int(t.size())*8 < e.w || a.survivesSpill(f, t) {
		// A bool's consumers look only at its low byte. And if x's
		// type is narrower than the extension, the extension reads
		// bits of x that are undefined anyway.
		return ""
	}
	x, rx := a.spillWitness(f, t)
	why := ot.explain(arg.Op, t)
	if why == "" {
		why = fmt.Sprintf("%s can have type %s", arg.Op.Name, t)
	}
	how := "sign-extended"
	if a.restoreZero || !t.signed() {
		how = "zero-extended"
	}
	return fmt.Sprintf("%s removed, so %s's register is used as is, but %s and a spilled %s is restored %s: %s comes back as %s",
		ename, arg.Name, why, t, how, a.hex(x), a.hex(rx))
}

// constsFit reports whether, in w, the constant args of n's nodes fit
// the node's type, as a constant from a generic ConstN would: an AND of
// type uint16 has no constant arg 0xffff (it would be -1).
func constsFit(n *rules.Value, w world) bool {
	ok := true
	n.Walk(func(m *rules.Value) bool {
		t, has := w.typeOf(m)
		if !has || m.Op == nil {
			return ok
		}
		for _, a := range m.Args {
			if a.Op == nil || !constOpRE.MatchString(a.Op.Name) {
				continue
			}
			var c val
			if rules.IsVarText(a.AuxInt) {
				c = w.env[a.AuxInt]
			} else {
				c = evalString(a.AuxInt, nil)
			}
			if c.k.isInt() && fitting(c.i, setOf(t)) == 0 {
				ok = false
			}
		}
		return ok
	})
	return ok
}

func hasAuxVars(n *rules.Value) bool {
	found := false
	n.Walk(func(m *rules.Value) bool {
		if m.Op != nil && rules.IsVarText(m.AuxInt) {
			found = true
		}
		return !found
	})
	return found
}

func extended(e ext) string {
	if e.signed {
		return fmt.Sprintf("sign-extended from %d bits", e.w)
	}
	return fmt.Sprintf("zero-extended from %d bits", e.w)
}

func nodeDesc(n *rules.Value) string {
	s := n.Op.Name
	if n.AuxInt != "" {
		s += " [" + n.AuxInt + "]"
	}
	return s
}

// worldDesc describes the auxint values of n in w, such as " when c=3".
func worldDesc(n *rules.Value, w world) string {
	s := ""
	n.Walk(func(m *rules.Value) bool {
		if m.Op != nil && rules.IsVarText(m.AuxInt) {
			if v, ok := w.env[m.AuxInt]; ok && v.k.isInt() {
				sep := " when "
				if s != "" {
					sep = ", "
				}
				if v.k == kBitField {
					s += fmt.Sprintf("%s%s=ArmBFAuxInt(%d, %d)", sep, m.AuxInt, uint64(v.i)>>8, v.i&0xff)
				} else {
					s += fmt.Sprintf("%s%s=%d", sep, m.AuxInt, v.i)
				}
			}
		}
		return true
	})
	return s
}

// factWitness returns a register value x satisfying f that e changes,
// and e(x).
func (a *archInfo) factWitness(f fact, e ext) (x, ex int64) {
	switch {
	case !e.signed && f.zm < a.regBits:
		x = int64(1)<<f.zm - 1
	case !e.signed:
		x = -1
	default:
		x = int64(1) << (e.w - 1)
	}
	return x, applyExt(x, e)
}

// spillWitness returns a register value x satisfying f, of a value of type
// t, that a spill and restore changes, and the restored value.
func (a *archInfo) spillWitness(f fact, t ssaType) (x, rx int64) {
	n := int(t.size()) * 8
	r := a.restored(t, fact{a.regBits, a.regBits})
	re := ext{signed: r.sm <= n && r.zm > n, w: n}
	switch {
	case !re.signed && f.zm >= a.regBits:
		x = -(int64(1) << (min(f.sm, a.regBits) - 1)) // most negative
	case !re.signed:
		x = int64(1)<<f.zm - 1
	default:
		x = int64(1) << (n - 1)
	}
	return x, applyExt(x, re)
}

func applyExt(x int64, e ext) int64 {
	if e.signed {
		return x << (64 - e.w) >> (64 - e.w)
	}
	return int64(uint64(x) << (64 - e.w) >> (64 - e.w))
}

func (a *archInfo) hex(x int64) string {
	if a.regBits == 32 {
		return fmt.Sprintf("%#08x", uint32(x))
	}
	return fmt.Sprintf("%#016x", uint64(x))
}

// auxDomain returns the auxint values to try for an auxint of kind k:
// small numbers, powers of two and their neighbors, and masks.
func auxDomain(k kind) []val {
	if k == kBitField {
		var vs []val
		for lsb := int64(0); lsb < 64; lsb++ {
			for w := int64(1); lsb+w <= 64; w++ {
				vs = append(vs, intVal(k, w|lsb<<8))
			}
		}
		return vs
	}
	seen := map[int64]bool{}
	var vs []val
	add := func(x int64) {
		x = k.wrap(x)
		if !seen[x] {
			seen[x] = true
			vs = append(vs, intVal(k, x))
		}
	}
	// Try likely values first: the first wrong world is the one reported.
	for x := int64(1); x <= 65; x++ {
		add(x)
	}
	for x := int64(0); x >= -65; x-- {
		add(x)
	}
	for i := range 64 {
		p := int64(1) << i
		add(p)
		add(p - 1)
		add(p + 1)
		add(-p)
		add(^(p - 1))
	}
	return vs
}

func typeVals(ts typeSet) []val {
	var vs []val
	for _, t := range ts.all() {
		vs = append(vs, val{k: kType, t: t})
	}
	return vs
}

var exprCache sync.Map // string -> ast.Expr (nil if it does not parse)

func evalString(s string, en env) val {
	e, ok := exprCache.Load(s)
	if !ok {
		x, err := parser.ParseExpr(s)
		if err != nil {
			x = nil
		}
		e, _ = exprCache.LoadOrStore(s, x)
	}
	x, _ := e.(ast.Expr)
	if x == nil {
		return unknown
	}
	return eval(x, en)
}

var zeroUpperRE = regexp.MustCompile(`^zeroUpper(\d+)Bits$`)

// helperBits returns N if cond calls zeroUpperNBits(x, ...), which accepts
// values whose op has a zeroUpperBits attribute of at least N.
func helperBits(cond ast.Expr, x string) int {
	n := 0
	ast.Inspect(cond, func(nd ast.Node) bool {
		call, ok := nd.(*ast.CallExpr)
		if !ok || len(call.Args) == 0 || !mentions(call.Args[0], x) {
			return true
		}
		if _, name := funcName(call.Fun); zeroUpperRE.MatchString(name) {
			n, _ = strconv.Atoi(zeroUpperRE.FindStringSubmatch(name)[1])
		}
		return true
	})
	return n
}

// checkPhase checks that the op an elision relies on is not rewritten,
// in the same pass or a later one, into an op that lacks the fact.
//
// An extension's argument usually has a narrow type, whose upper bits
// rules may change at will. So if (MOVWUreg x:(MULW _ _)) => x runs in
// the same pass as a rule that rewrites MULW into an op that does not
// zero the upper half, the order in which the two apply decides whether
// the result is correct.
func (c *checker) phaseProblem(a *archInfo, r *rules.Rule, e ext) string {
	arg := r.Match.Args[0]
	if classify(a, r, arg) != passes {
		return ""
	}
	var relied []*ops.Op
	var helper map[*ops.Op]bool // if arg is vouched for by a helper
	bits := 0
	switch {
	case arg.Op == nil:
		if r.CondExpr == nil {
			return ""
		}
		if bits = helperBits(r.CondExpr, arg.Name); bits == 0 {
			return ""
		}
		helper = zeroUpperOps(r.Set.Arch, bits)
		for _, op := range r.Set.Arch.Ops {
			if helper[op] {
				relied = append(relied, op)
			}
		}
	case arg.Op.IsGeneric():
		return ""
	default:
		if _, src := a.opFact(arg, world{}); src == srcNone {
			return ""
		}
		relied = []*ops.Op{arg.Op}
	}

	pos := slices.Index(passOrder, r.Set.Suffix)
	ot := c.opTypes(r.Set)
	for _, set := range c.pass.Corpus.Sets {
		if set.Arch != r.Set.Arch || slices.Index(passOrder, set.Suffix) < pos {
			continue
		}
		for _, op := range relied {
			for _, rr := range set.ByOp[op] {
				if rr.Result == nil || rr.Match.Ellipsis {
					continue
				}
				if _, ok := elision(a, rr); ok && c.problem(a, rr) != "" {
					continue // a wrong elision, reported on its own
				}
				f, ok := hazard(a, ot, r, arg, e, bits, helper, rr)
				if !ok {
					continue
				}
				what := "x"
				if arg.Op != nil {
					what = arg.Op.Name
				}
				where := "later in the same pass"
				if set != r.Set {
					where = "in the later " + set.Name() + " pass"
				}
				return fmt.Sprintf("%s removed because %s is %s, but %s:%d may rewrite that %s %s into %s, which is %s",
					r.Match.Op.Name, what, extended(e), baseName(rr.Pos.File), rr.Pos.Line, op.Name, where, resultDesc(rr), f)
			}
		}
	}
	return ""
}

// hazard reports whether rr, a rule for the op of the value that the
// elision rule r relies on, can rewrite that value into one whose
// register does not satisfy e. It returns the result's fact.
//
// It matches rr's pattern against r's (so that a rule for ANDconst [-1]
// is not taken to rewrite the ANDconst [c] of an elision that requires
// c <= 0xff) and enumerates the auxints of both.
func hazard(a *archInfo, ot *opTypes, r *rules.Rule, arg *rules.Value, e ext, bits int, helper map[*ops.Op]bool, rr *rules.Rule) (fact, bool) {
	u := &unifier{leaf: map[string]*rules.Value{}, alias: map[string]string{}, fixedR: map[string]val{}, fixedE: map[string]val{}}
	if arg.Op != nil && !u.unify(arg, rr.Match) {
		return fact{}, false
	}
	bound := map[string]*rules.Value{}
	rr.Match.Walk(func(n *rules.Value) bool {
		if n.Op != nil && rules.IsVarText(n.Name) {
			bound[n.Name] = n
		}
		return true
	})

	// A slot is a variable to enumerate. Auxints belong to one rule or,
	// unified, to both; the matched value's type to both.
	type slot struct {
		e, r []string       // names in the elision's and rr's environments
		node []*rules.Value // match nodes whose type it is
		vals []val
	}
	var slots []slot
	if arg.Op != nil {
		arg.Walk(func(n *rules.Value) bool {
			if n.Op != nil && rules.IsVarText(n.AuxInt) {
				if k, ok := kindNames[n.Op.AuxIntType]; ok {
					slots = append(slots, slot{e: []string{n.AuxInt}, vals: auxDomain(k)})
				}
			}
			return true
		})
	}
	rr.Match.Walk(func(n *rules.Value) bool {
		if n.Op == nil {
			return true
		}
		if rules.IsVarText(n.AuxInt) && u.alias[n.AuxInt] == "" && u.fixedR[n.AuxInt].k == kUnknown {
			if k, ok := kindNames[n.Op.AuxIntType]; ok {
				slots = append(slots, slot{r: []string{n.AuxInt}, vals: auxDomain(k)})
			}
		}
		if n != rr.Match && n.Op.Name == "Arg" && rules.IsVarText(n.Type) {
			slots = append(slots, slot{r: []string{n.Type}, node: []*rules.Value{n}, vals: typeVals(allTypes)})
		}
		return true
	})
	// The type of the value both rules match.
	ts := slot{r: []string{"v.Type"}, node: []*rules.Value{rr.Match}}
	if rules.IsVarText(rr.Match.Type) {
		ts.r = append(ts.r, rr.Match.Type)
	}
	if arg.Op != nil {
		ts.node = append(ts.node, arg)
		if rules.IsVarText(arg.Name) {
			ts.e = append(ts.e, arg.Name+".Type")
		}
		if rules.IsVarText(arg.Type) {
			ts.e = append(ts.e, arg.Type)
		}
		ts.vals = typeVals(ot.ofNode(arg))
	} else {
		ts.vals = typeVals(ot.ofNode(rr.Match))
	}
	if len(ts.vals) > 0 {
		slots = append(slots, ts)
	}

	size := 1
	for _, s := range slots {
		size *= len(s.vals)
	}
	if size == 0 || size > 1<<16 {
		return fact{}, false
	}

	idx := make([]int, len(slots))
	for {
		envE, envR := env{}, env{}
		types := map[*rules.Value]ssaType{}
		for i, s := range slots {
			v := s.vals[idx[i]]
			for _, n := range s.e {
				envE[n] = v
			}
			for _, n := range s.r {
				envR[n] = v
			}
			for _, n := range s.node {
				types[n] = v.t
			}
		}
		for rn, en := range u.alias {
			envR[rn] = envE[en]
		}
		for rn, v := range u.fixedR {
			envR[rn] = v
		}
		ok := true
		for en, v := range u.fixedE {
			if envE[en].k.isInt() && envE[en].i != v.i {
				ok = false
			}
		}
		wE := world{env: envE, types: types}
		wR := world{env: envR, types: types, leaf: map[string]fact{}, bound: bound}
		if ok && mayHold(r.CondExpr, envE) && mayHold(rr.CondExpr, envR) && (arg.Op == nil || a.validAux(arg, wE) && constsFit(arg, wE)) && a.validAux(rr.Match, wR) && constsFit(rr.Match, wR) {
			pre := true
			if arg.Op != nil {
				f0, _ := a.opFact(arg, wE)
				pre = f0.holds(e)
			}
			if pre {
				for name, n := range u.leaf {
					wR.leaf[name], _ = a.opFact(n, wE)
				}
				if rr.CondExpr != nil {
					rr.Match.Walk(func(n *rules.Value) bool {
						if n.IsVar() {
							if b := helperBits(rr.CondExpr, n.Name); b > 0 {
								wR.leaf[n.Name] = zeroFrom(64 - b).cap(a.regBits)
							}
						}
						return true
					})
				}
				if f, ok := a.resultFact(rr, bits, helper, wR); ok && !f.holds(e) {
					return f, true
				}
			}
		}
		i := 0
		for ; i < len(slots); i++ {
			idx[i]++
			if idx[i] < len(slots[i].vals) {
				break
			}
			idx[i] = 0
		}
		if i == len(slots) {
			return fact{}, false
		}
	}
}

func mayHold(cond ast.Expr, en env) bool {
	if cond == nil {
		return true
	}
	c := eval(cond, en)
	return c.k != kBool || c.b
}

// A unifier matches the pattern of a rule for an op against the pattern
// of an elision rule's argument with that op.
type unifier struct {
	leaf   map[string]*rules.Value // rr's leaf variables, bound to the elision's nodes
	alias  map[string]string       // rr's auxint variables, equal to the elision's
	fixedR map[string]val          // rr's auxint variables, equal to the elision's literals
	fixedE map[string]val          // the elision's auxint variables, equal to rr's literals
}

func (u *unifier) unify(e, m *rules.Value) bool {
	if m.Op == nil {
		if m.IsVar() {
			u.leaf[m.Name] = e
		}
		return true
	}
	if e.Op == nil {
		return true
	}
	if e.Op != m.Op || m.Ellipsis || e.Ellipsis {
		return false
	}
	ev, mv := rules.IsVarText(e.AuxInt), rules.IsVarText(m.AuxInt)
	switch {
	case e.AuxInt == "" || m.AuxInt == "" || e.AuxInt == "_" || m.AuxInt == "_":
	case ev && mv:
		u.alias[m.AuxInt] = e.AuxInt
	case ev:
		u.fixedE[e.AuxInt] = intVal(kInt64, evalString(m.AuxInt, nil).i)
	case mv:
		u.fixedR[m.AuxInt] = intVal(kInt64, evalString(e.AuxInt, nil).i)
	default:
		if evalString(e.AuxInt, nil) != evalString(m.AuxInt, nil) {
			return false
		}
	}
	if len(e.Args) != len(m.Args) {
		return true // a ___ pattern: don't look further
	}
	for i := range e.Args {
		if !u.unify(e.Args[i], m.Args[i]) {
			return false
		}
	}
	return true
}

// resultFact returns the fact of rr's result in w, if known. If helper is
// not nil, the fact relied on is that a zeroUpperNBits helper (N = bits)
// accepts the value, and a result op it does not accept lacks the fact.
func (a *archInfo) resultFact(rr *rules.Rule, bits int, helper map[*ops.Op]bool, w world) (fact, bool) {
	res := rr.Result
	if res.IsLeaf() && !res.IsVar() {
		return fact{}, false
	}
	f, src := a.opFact(res, w)
	if src == srcExact {
		return f, true
	}
	if helper == nil {
		return fact{}, false
	}
	op := res.Op
	if res.IsLeaf() {
		if n := w.bound[res.Name]; n != nil {
			op = n.Op
		}
	}
	if op != nil && helper[op] {
		return zeroFrom(64 - bits).cap(a.regBits), true
	}
	if op != nil && op.IsGeneric() {
		return fact{}, false
	}
	return f, true
}

func resultDesc(r *rules.Rule) string {
	if r.Result.IsLeaf() {
		return r.Result.Name
	}
	return r.Result.Text
}
