package condsem

import (
	"fmt"
	"go/ast"
	"go/types"
	"sort"
	"strings"

	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// want describes what an op expects of an argument, which determines the
// domain a leaf variable in that position ranges over.
type want struct {
	k    kind // kInt, kFloat, kFlags, or kSym for "anything"
	w    uint8
	bool bool // kInt restricted to 0 and 1
	cat  fcat // kFlags: the categories of flags the consumer reads
	inv  bool // kFlags: the operand of InvertFlags
}

var (
	wAny  = want{k: kSym}
	wBool = want{k: kInt, w: 8, bool: true}
)

func rng(lo, hi int64) *[2]int64 { return &[2]int64{lo, hi} }

func wInt(w uint8) want   { return want{k: kInt, w: w} }
func wFloat(w uint8) want { return want{k: kFloat, w: w} }
func wFlags(c fcat) want  { return want{k: kFlags, cat: c} }
func wFlagsInv() want     { return want{k: kFlags, cat: catBoth, inv: true} }
func wInts(n int, w uint8) []want {
	ws := make([]want, n)
	for i := range ws {
		ws[i] = wInt(w)
	}
	return ws
}

// opSem is the semantics of an op.
type opSem struct {
	args []want
	// inherit makes the flags argument's category that of the op's own
	// use (InvertFlags).
	inherit bool
	// ccArg, if nonzero, is 1 + the index of a flags argument whose
	// category is that of the condition named by the auxint (CSEL).
	ccArg int
	// auxRange, if set, is the range of auxint values the op allows
	// (such as shift amounts); a match with others is impossible.
	auxRange *[2]int64
	// origin is the kind of flags the op produces, for producers.
	origin origin
	eval   func(c *ctx, n *node) val
}

// blockSem is the semantics of a block kind with a decision to make.
type blockSem struct {
	controls []want
	// test names the condition codegen branches on, such as "MI".
	test string
	// eval reports whether the block takes its first successor.
	eval func(c *ctx, n *node) bool
}

// node is an op's evaluated aux fields and args.
type node struct {
	op     string
	auxint gv
	aux    gv
	args   []val
}

func (n *node) auxInt() int64 {
	if n.auxint.k != gInt {
		unmodeled("%s auxint is %v", n.op, n.auxint)
	}
	return int64(n.auxint.i)
}

func (n *node) auxOp() string {
	if n.auxint.k != gOp {
		unmodeled("%s auxint is %v", n.op, n.auxint)
	}
	return n.auxint.s
}

// ctx evaluates one rule under one assignment of its variables.
type ctx struct {
	a    *arch
	r    *rules.Rule
	tr   *typecheck.Rule
	info *types.Info
	en   *enumerator
	lits []uint64

	env     map[string]val // match variables (values)
	genv    map[string]gv  // match variables (aux fields)
	order   []string       // variables in order of binding, for messages
	promote map[string]want
	alias   map[string]string // from x == y conditions on values
	limit   int               // domain prefix length per choice

	// matchName and resultName name the sides' root ops, for messages.
	matchName, resultName string
	leafNote              string
	// shadowed are root auxints the match is not to take, because
	// earlier rules handle them (see shadowedAux).
	shadowed map[int64]bool

	onResult bool  // evaluating the result side
	root     *node // the match's root op
	idom     []uint64
	mem      map[string]uint64 // contents of memory, by address and memory state
}

// load returns the w-bit value at ptr+off+{sym} in memory state mem.
func (c *ctx) load(n *node, ptr val, off gv, mem val, w uint8) uint64 {
	var addr string
	if ptr.k == kInt && off.k == gInt {
		addr = fmt.Sprint(ptr.i + off.i)
	} else {
		addr = fmt.Sprintf("%v+%v", ptr, off)
	}
	key := fmt.Sprintf("%s {%v} %v %d", addr, n.aux, mem, w)
	if x, ok := c.mem[key]; ok {
		return x
	}
	d := c.intDomain()
	x := trunc(d[c.choose(len(d))], w)
	c.mem[key] = x
	return x
}

type restart struct{}

// choose returns an element of a domain of size n.
func (c *ctx) choose(n int) int {
	if n > c.limit {
		n = c.limit
	}
	return c.en.choose(n)
}

func (c *ctx) bindLeaf(name string, w want) val {
	if v, ok := c.env[name]; ok {
		return c.coerce(name, v, w)
	}
	if t, ok := c.alias[name]; ok {
		if v, ok := c.env[t]; ok {
			c.env[name] = v
			return c.coerce(name, v, w)
		}
	}
	if p, ok := c.promote[name]; ok {
		w = p
	}
	v := c.fresh(name, w)
	c.env[name] = v
	c.order = append(c.order, name)
	return v
}

// coerce checks that a bound variable's value suits a use.
func (c *ctx) coerce(name string, v val, w want) val {
	switch {
	case w.k == kSym:
		return v
	case v.k == kSym:
		// First bound as an opaque value, now used concretely.
		// Restart, binding it concretely from the start.
		if c.promote[name].k != kNone {
			unmodeled("conflicting uses of %s", name)
		}
		c.promote[name] = w
		panic(restart{})
	case v.k != w.k:
		unmodeled("%s used as both %v and %v", name, v.k, w.k)
	case w.k == kFlags && w.inv && !c.a.invertible(v.fl):
		impossible()
	}
	return v
}

// fresh returns a value for a new variable.
func (c *ctx) fresh(name string, w want) val {
	switch w.k {
	case kSym:
		return symVal(name)
	case kInt:
		if w.bool {
			return intVal(uint64(c.choose(2)), 8)
		}
		d := c.intDomain()
		return intVal(d[c.choose(len(d))], 64)
	case kFloat:
		f := floatDomain[c.choose(len(floatDomain))]
		return floatVal(f, w.w)
	case kFlags:
		d := c.a.flagDomain(w.cat, w.inv)
		if len(d) == 0 {
			impossible() // no such flags in this context
		}
		return val{k: kFlags, fl: d[c.choose(len(d))]}
	}
	unmodeled("variable %s of kind %v", name, w.k)
	return val{}
}

func (c *ctx) intDomain() []uint64 {
	if c.idom != nil {
		return c.idom
	}
	c.idom = c.makeIntDomain()
	return c.idom
}

func (c *ctx) makeIntDomain() []uint64 {
	if len(c.lits) == 0 {
		return intDomain
	}
	// Literals of the rule and their neighbors come first.
	d := make([]uint64, 0, len(intDomain)+3*len(c.lits))
	seen := make(map[uint64]bool)
	add := func(x uint64) {
		if !seen[x] {
			seen[x] = true
			d = append(d, x)
		}
	}
	for _, x := range intDomain[:4] {
		add(x)
	}
	for _, l := range c.lits {
		add(l)
		add(l - 1)
		add(l + 1)
	}
	for _, x := range intDomain {
		add(x)
	}
	return d
}

// match evaluates a match s-expression.
func (c *ctx) match(v *rules.Value, w want) val {
	if v.IsLeaf() {
		if v.Name == "_" {
			return c.fresh("_", w)
		}
		return c.bindLeaf(v.Name, w)
	}
	if v.Ellipsis || v.Rest {
		unmodeled("variadic match")
	}
	sem := c.a.sem(v.Op)
	n := &node{op: v.Op.Name}
	n.auxint = c.matchAux(v, v.AuxInt, typecheck.AuxInt)
	n.aux = c.matchAux(v, v.Aux, typecheck.Aux)
	if r := sem.auxRange; r != nil {
		if n.auxint.k == gTop {
			unmodeled("%s without auxint", n.op)
		}
		if k := n.auxInt(); k < r[0] || k > r[1] {
			impossible()
		}
	}
	args := sem.args
	if sem.inherit && w.k == kFlags {
		args = []want{{k: kFlags, cat: w.cat, inv: true}}
	}
	if sem.ccArg > 0 && n.auxint.k == gOp {
		if cd := c.a.ccOps[n.auxint.s]; cd != nil {
			args = append([]want(nil), args...)
			args[sem.ccArg-1].cat = cd.cat
		}
	}
	if len(v.Args) != len(args) {
		unmodeled("%s with %d args", v.Op.Name, len(v.Args))
	}
	for i, a := range v.Args {
		if a.IsLeaf() && a.Name == "_" {
			n.args = append(n.args, c.fresh(fmt.Sprintf("%s's arg %d", v.Op.Name, i), args[i]))
			continue
		}
		n.args = append(n.args, c.match(a, args[i]))
	}
	if v == c.r.Match {
		c.root = n
		if n.auxint.k == gInt && c.shadowed[int64(n.auxint.i)] {
			impossible()
		}
	}
	x := c.checkKind(v, sem.eval(c, n), w)
	if v.Name != "" {
		if old, ok := c.env[v.Name]; ok {
			// x:(...) repeated: an equality constraint.
			if !c.same(old, x) {
				impossible()
			}
		} else {
			c.env[v.Name] = x
		}
	}
	return x
}

// matchAux evaluates the [auxint] or {aux} of a match node: binding a
// variable, or evaluating the expression it is compared against.
func (c *ctx) matchAux(v any, text string, f typecheck.Field) gv {
	if text == "" || text == "_" {
		return top
	}
	if !rules.IsVarText(text) {
		return c.goExpr(c.tr.Expr(v, f))
	}
	if x, ok := c.genv[text]; ok {
		return x
	}
	var t types.Type
	if tv := c.tr.Vars[text]; tv != nil {
		t = tv.Type()
	}
	x := c.freshAux(text, t)
	c.genv[text] = x
	c.order = append(c.order, text)
	return x
}

// freshAux returns a value for a new aux variable of Go type t.
func (c *ctx) freshAux(name string, t types.Type) gv {
	if t == nil {
		return gv{k: gSym, s: name}
	}
	if n, ok := t.(*types.Named); ok {
		switch n.Obj().Name() {
		case "Op":
			ccs := c.a.ccOpNames
			if len(ccs) == 0 {
				unmodeled("op-valued aux %s", name)
			}
			return gv{k: gOp, s: ccs[c.choose(len(ccs))], t: t}
		case "FlagConstant", "flagConstant":
			return gv{k: gInt, i: uint64(c.choose(16)), t: t}
		case "CCMask":
			// An s390x condition code mask.
			return gv{k: gInt, i: uint64(c.choose(16)), t: t}
		case "ValAndOff":
			// A 32-bit value and a 32-bit offset (ssa/op.go).
			vals := []int32{0, 1, -1, 0x7f, 0x80, 0x7fff, 0x8000, 0x7fffffff, -0x80000000, 0xff, 0xffff, -2}
			offs := []int32{0, 8}
			v := vals[c.choose(len(vals))]
			o := offs[c.choose(len(offs))]
			return gv{k: gInt, i: uint64(int64(v)<<32 | int64(uint32(o))), t: t}
		}
	}
	b, ok := t.Underlying().(*types.Basic)
	if !ok {
		return gv{k: gSym, s: name, t: t}
	}
	switch {
	case b.Info()&types.IsBoolean != 0:
		return gv{k: gBool, b: c.choose(2) == 1, t: t}
	case b.Info()&types.IsInteger != 0:
		if _, named := t.(*types.Named); named {
			return gv{k: gSym, s: name, t: t} // ValAndOff and the like
		}
		d := c.intDomain()
		return mkInt(d[c.choose(len(d))], t)
	case b.Info()&types.IsFloat != 0:
		return gv{k: gFloat, f: floatDomain[c.choose(len(floatDomain))], t: t}
	}
	return gv{k: gSym, s: name, t: t}
}

// badAux handles an op's auxint that is outside the values the op
// supports: such a match can't happen, but such a result is wrong.
func (c *ctx) badAux(n *node, k int64) {
	if c.onResult {
		panic(mismatch{fmt.Sprintf("the result's %s has auxint %d, outside its range", n.op, k)})
	}
	impossible()
}

// result evaluates a result s-expression.
func (c *ctx) result(v *rules.Value, w want) val {
	if v.IsLeaf() {
		if !v.IsVar() {
			unmodeled("result expression %s", v.Name)
		}
		x, ok := c.env[v.Name]
		if !ok {
			unmodeled("result variable %s is not a value", v.Name)
		}
		return c.coerce(v.Name, x, w)
	}
	if v.Ellipsis {
		unmodeled("ellipsis result")
	}
	sem := c.a.sem(v.Op)
	n := &node{op: v.Op.Name}
	n.auxint = c.resultAux(v, v.AuxInt, typecheck.AuxInt)
	n.aux = c.resultAux(v, v.Aux, typecheck.Aux)
	if len(v.Args) != len(sem.args) {
		unmodeled("%s with %d args", v.Op.Name, len(v.Args))
	}
	for i, a := range v.Args {
		n.args = append(n.args, c.result(a, sem.args[i]))
	}
	return c.checkKind(v, sem.eval(c, n), w)
}

// checkKind checks that an op's value suits its use.
func (c *ctx) checkKind(v *rules.Value, x val, w want) val {
	if w.k != kSym && x.k != w.k {
		unmodeled("%s is %v, used as %v", v.Op.Name, x.k, w.k)
	}
	return x
}

func (c *ctx) resultBlockAux(b *rules.Block, text string, f typecheck.Field) gv {
	if text == "" {
		return gv{k: gInt}
	}
	if x, ok := c.genv[text]; ok {
		return x
	}
	e := c.tr.Expr(b, f)
	if e == nil {
		unmodeled("no typed expression for %s", text)
	}
	return c.goExpr(e)
}

func (c *ctx) resultAux(v *rules.Value, text string, f typecheck.Field) gv {
	if text == "" {
		return gv{k: gInt} // results zero unset aux fields
	}
	if x, ok := c.genv[text]; ok {
		return x
	}
	e := c.tr.Expr(v, f)
	if e == nil {
		unmodeled("no typed expression for %s", text)
	}
	return c.goExpr(e)
}

// block evaluates a block s-expression, returning the successor taken.
func (c *ctx) block(b *rules.Block, isMatch bool) string {
	if b.Kind == "First" {
		if len(b.Succs) == 0 {
			return "yes"
		}
		return b.Succs[0]
	}
	sem := c.a.blockSem(b.Info)
	n := &node{op: b.Info.Name}
	if isMatch {
		n.auxint = c.matchAux(b, b.AuxInt, typecheck.AuxInt)
		n.aux = c.matchAux(b, b.Aux, typecheck.Aux)
	} else {
		n.auxint = c.resultBlockAux(b, b.AuxInt, typecheck.AuxInt)
		n.aux = c.resultBlockAux(b, b.Aux, typecheck.Aux)
	}
	if len(b.Controls) != len(sem.controls) {
		unmodeled("%s with %d controls", b.Info.Name, len(b.Controls))
	}
	for i, ctl := range b.Controls {
		if isMatch {
			n.args = append(n.args, c.match(ctl, sem.controls[i]))
		} else {
			n.args = append(n.args, c.result(ctl, sem.controls[i]))
		}
	}
	succs := b.Succs
	if len(succs) == 0 {
		succs = []string{"yes", "no"} // the successors are kept as they are
	}
	if len(succs) != 2 {
		unmodeled("block with %d successors", len(b.Succs))
	}
	if sem.eval(c, n) {
		return succs[0]
	}
	return succs[1]
}

// same reports whether two values are indistinguishable.
func (c *ctx) same(x, y val) bool {
	ok, _ := c.compare(x, y)
	return ok
}

// compare reports whether the result value r computes the same thing as
// the match value m. If not, it describes the difference.
func (c *ctx) compare(m, r val) (bool, string) {
	differ := func() (bool, string) {
		mn, rn := "the match", "the result"
		if c.matchName != "" {
			mn += " (" + c.matchName + ")"
		}
		if c.resultName != "" {
			rn += " (" + c.resultName + ")"
		}
		if m.k == kSucc {
			return false, fmt.Sprintf("%s branches to %v but %s to %v", mn, m, rn, r)
		}
		return false, fmt.Sprintf("%s yields %v but %s yields %v%s", mn, m, rn, r, c.leafNote)
	}
	if m.k != r.k {
		return differ()
	}
	switch m.k {
	case kInt:
		w := min(m.w, r.w)
		if trunc(m.i, w) != trunc(r.i, w) {
			return differ()
		}
	case kFloat:
		if !(m.f == r.f || m.f != m.f && r.f != r.f) {
			return differ()
		}
	case kSym, kSucc:
		if m.s != r.s {
			return differ()
		}
	case kFlags:
		return c.compareFlags(m.fl, r.fl)
	case kStore, kTuple:
		if len(m.xs) != len(r.xs) || m.s != r.s {
			return differ()
		}
		for i := range m.xs {
			if ok, d := c.compare(m.xs[i], r.xs[i]); !ok {
				return false, d
			}
		}
	}
	return true, ""
}

func (c *ctx) compareFlags(m, r *flags) (bool, string) {
	cat := catInt
	if m.o == oFloat {
		cat = catFloat
	}
	for _, cd := range c.a.conds {
		if cd.cat&cat == 0 {
			continue
		}
		if m.o == oArith && cd.name != "CS" {
			// The flags of carry-chain arithmetic (NEGLflags, ADCQ, ...)
			// exist to feed carry chains (ADCQ, SBBQ, SETB) and are
			// compared only on the carry.
			continue
		}
		mt, rt := cd.eval(m), cd.eval(r)
		if !mt.known() || rt == tSkip || mt == rt {
			continue
		}
		switch {
		case rt == tStale:
			return false, fmt.Sprintf("condition %s holds %v for the match's flags %v, but the result's flags %v leave it undefined", cd.name, mt, m, r)
		case mt == tTrue:
			return false, fmt.Sprintf("condition %s holds for the match's flags %v but not for the result's flags %v", cd.name, m, r)
		default:
			return false, fmt.Sprintf("condition %s holds for the result's flags %v but not for the match's flags %v", cd.name, r, m)
		}
	}
	return true, ""
}

// bindings describes the variables' current values.
func (c *ctx) bindings() string {
	var s []string
	for _, name := range c.order {
		if v, ok := c.env[name]; ok {
			if v.k == kSym {
				continue
			}
			s = append(s, name+" = "+v.String())
		} else if g, ok := c.genv[name]; ok {
			if g.k == gSym || g.k == gTop {
				continue
			}
			s = append(s, name+" = "+g.String())
		}
	}
	return strings.Join(s, ", ")
}

// enumerator enumerates the paths through a tree of choices, depth first.
type enumerator struct {
	choices []int
	sizes   []int
	pos     int
}

func (e *enumerator) choose(n int) int {
	if e.pos < len(e.choices) {
		c := e.choices[e.pos]
		if c >= n {
			// The tree's shape changed under us; treat as the last option.
			c = n - 1
			e.choices[e.pos] = c
			e.sizes[e.pos] = n
		}
		e.pos++
		return c
	}
	e.choices = append(e.choices, 0)
	e.sizes = append(e.sizes, n)
	e.pos++
	return 0
}

// next advances to the next path, reporting whether there is one.
func (e *enumerator) next() bool {
	e.choices = e.choices[:e.pos]
	e.sizes = e.sizes[:e.pos]
	e.pos = 0
	for i := len(e.choices) - 1; i >= 0; i-- {
		e.choices[i]++
		if e.choices[i] < e.sizes[i] {
			e.choices = e.choices[:i+1]
			e.sizes = e.sizes[:i+1]
			return true
		}
	}
	return false
}

// conjuncts splits a condition into its && operands.
func conjuncts(e ast.Expr) []ast.Expr {
	if p, ok := e.(*ast.ParenExpr); ok {
		return conjuncts(p.X)
	}
	if b, ok := e.(*ast.BinaryExpr); ok && b.Op.String() == "&&" {
		return append(conjuncts(b.X), conjuncts(b.Y)...)
	}
	return []ast.Expr{e}
}

func (k kind) String() string {
	return [...]string{"none", "int", "float", "flags", "value", "successor", "store", "tuple"}[k]
}

func sortStrings(s []string) { sort.Strings(s) }
