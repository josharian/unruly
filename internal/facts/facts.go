// Package facts proves bounds on the integer Go expressions of a rule:
// that an auxint fits its type, that a shift count is in range, that a
// divisor is nonzero, and so on.
//
// For a rule
//
//	(ADDQconst [c] (ADDQconst [d] x)) && is32Bit(int64(c)+int64(d)) => (ADDQconst [c+d] x)
//
// New derives facts from what is known when the rule fires: the types of
// the match variables (c and d are int32, from ADDQconst's auxint type)
// and the condition. Queries then bound any expression of the rule, such
// as the result's c+d (see typecheck.Rule.Expr):
//
//	f := facts.New(res, rule)
//	f.Range(e)     // [-2147483648, 2147483647]: c+d's value, which is an int32
//	f.Exact(e)     // true: c+d does not wrap around, because of is32Bit
//
// Other queries ask whether an expression lies in a range (In), fits in a
// type (Fits), or is nonzero (NonZero), and which of its operations may
// wrap around (Overflows, OverflowsMod). AssumeVar adds knowledge about a
// variable, such as an op's auxint domain.
//
// Facts come from the condition's comparisons, ==, !=, &&, ||, and !,
// with helpers like is32Bit, isU12Bit, and isPowerOfTwo understood by
// reading their definitions in the Go tree: a helper whose body is a
// single return statement (after any x := e definitions) is inlined. So
// are integer-valued helpers like log64 and ntz32, and methods like
// ValAndOff.Val. Bounds propagate through integer conversions,
// arithmetic, masks (x & 0xff), %, /, shifts, min, max, and math/bits
// functions.
//
// Arithmetic is Go's, with wraparound: Range(e) is the set of values e
// may have, and is always within e's type. Exact and Overflows say
// whether e's value is the mathematical value of its expression, that
// is, whether any operation or conversion in it may wrap around or
// truncate. Ints, uints, and uintptrs are 32 or 64 bits, depending on
// the compiler's host; facts treats their values as 64-bit but proves
// that a computation does not wrap only if it fits in 32 bits.
//
// Queries are sound but incomplete: a query that cannot be proved
// answers false (or the expression's whole type range), never true.
// A rule whose condition is unsatisfiable proves everything.
package facts

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"maps"
	"math/big"
	"slices"
	"strconv"

	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// Facts holds what is known about a rule's expressions when it fires.
type Facts struct {
	res   *typecheck.Result
	tr    *typecheck.Rule
	cond  ast.Expr
	vars  map[string]Interval // from AssumeVar
	nots  []assumption        // from AssumeNot
	ins   []within            // from AssumeIn
	excl  []exclusion         // from ExcludeVar
	store store
	root  *env
}

// env is the context of an expression: the rule's expressions, or the
// body of an inlined helper, whose parameters stand for the call's
// arguments.
type env struct {
	info  *types.Info
	bind  map[types.Object]binding
	depth int
}

type binding struct {
	e  ast.Expr
	en *env
}

// New returns the facts that hold when rule r of res fires.
// Queries take expressions of r from res, such as tr.Cond's
// sub-expressions and tr.Expr(rule.Result, typecheck.AuxInt).
func New(res *typecheck.Result, r *rules.Rule) *Facts {
	f := &Facts{res: res, root: &env{info: res.Info}}
	if tr := res.Rule(r); tr != nil {
		f.tr = tr
		f.cond = tr.Cond
	}
	f.derive()
	return f
}

// AssumeVar returns facts that also assume that the rule's match
// variable name lies in iv. Use it for knowledge about an op's auxint
// that its type does not express, such as that a shift's count is less
// than its width.
func (f *Facts) AssumeVar(name string, iv Interval) *Facts {
	g := &Facts{res: f.res, tr: f.tr, cond: f.cond, root: f.root, vars: maps.Clone(f.vars), nots: f.nots, ins: f.ins, excl: f.excl}
	if g.vars == nil {
		g.vars = make(map[string]Interval)
	}
	if old, ok := g.vars[name]; ok {
		iv = meet(old, iv)
	}
	g.vars[name] = iv
	g.derive()
	return g
}

// An assumption is a boolean expression assumed to have a value.
type assumption struct {
	e     ast.Expr
	en    *env
	truth bool
}

// AssumeNot returns facts that also assume that cond is false. Cond is
// an expression of the same rule set, typically the condition of an
// earlier rule for the same op, which must have been false for this rule
// to fire. Its free variables are given by bind: each variable obj of
// cond stands for expression bind[obj] of this rule, such as the
// identifier of the match variable at the same position. Identifiers of
// cond not in bind keep their meaning (v, config, helpers).
func (f *Facts) AssumeNot(cond ast.Expr, bind map[types.Object]ast.Expr) *Facts {
	en := &env{info: f.root.info, bind: make(map[types.Object]binding, len(bind))}
	for obj, e := range bind {
		en.bind[obj] = binding{e: e, en: f.root}
	}
	g := &Facts{res: f.res, tr: f.tr, cond: f.cond, root: f.root, vars: f.vars, ins: f.ins, excl: f.excl}
	g.nots = append(slices.Clip(f.nots), assumption{e: cond, en: en, truth: false})
	g.derive()
	return g
}

type within struct {
	e  ast.Expr
	iv Interval
}

// AssumeIn returns facts that also assume that e, an integer expression
// of the rule, lies in iv. Use it for knowledge that the condition does
// not state, such as that the auxint 64-c that a match compares against
// in (SRLconst x [64-c]) is in SRLconst's domain.
func (f *Facts) AssumeIn(e ast.Expr, iv Interval) *Facts {
	g := &Facts{res: f.res, tr: f.tr, cond: f.cond, root: f.root, vars: f.vars, nots: f.nots, excl: f.excl}
	g.ins = append(slices.Clip(f.ins), within{e, iv})
	g.derive()
	return g
}

type exclusion struct {
	name string
	x    *big.Int
}

// ExcludeVar returns facts that also assume that the rule's match
// variable name is not x. Use it for knowledge such as that an earlier,
// unconditional rule handles x: (Select0 (MULTU (MOVWconst [1]) _)) before
// (Select0 (MULTU (MOVWconst [c]) x)) means c != 1.
func (f *Facts) ExcludeVar(name string, x *big.Int) *Facts {
	g := &Facts{res: f.res, tr: f.tr, cond: f.cond, root: f.root, vars: f.vars, nots: f.nots, ins: f.ins}
	g.excl = append(slices.Clip(f.excl), exclusion{name, x})
	g.derive()
	return g
}

// derive computes the facts, iterating because facts about one
// expression can refine others.
func (f *Facts) derive() {
	f.store = store{m: make(map[string]fact)}
	for range 6 {
		f.store.changed = false
		for name, iv := range f.vars {
			f.store.meet("g:"+name, iv)
		}
		if f.cond != nil {
			f.assume(f.cond, f.root, true)
		}
		for _, a := range f.nots {
			f.assume(a.e, a.en, a.truth)
		}
		for _, w := range f.ins {
			f.constrain(w.e, f.root, w.iv)
		}
		for _, x := range f.excl {
			f.store.exclude("g:"+x.name, x.x)
		}
		if !f.store.changed || f.store.bottom {
			break
		}
	}
}

// Range returns the possible values of integer expression e,
// and false if e is not an integer expression.
func (f *Facts) Range(e ast.Expr) (Interval, bool) {
	if f.store.bottom {
		return Interval{one, zero}, isInt(f.typeOf(e, f.root))
	}
	return f.goRange(e, f.root)
}

// In reports whether e's value provably lies in [lo, hi].
func (f *Facts) In(e ast.Expr, lo, hi int64) bool {
	r, ok := f.Range(e)
	return ok && r.Within(Range(lo, hi))
}

// Fits reports whether e's value provably fits in integer type t, so that
// converting it to t preserves it. An int, uint, or uintptr t is taken to
// be 32 bits.
func (f *Facts) Fits(e ast.Expr, t types.Type) bool {
	r, ok := f.Range(e)
	tr, tok := safeRange(t)
	return ok && tok && r.Within(tr)
}

// NonZero reports whether e's value is provably not 0.
func (f *Facts) NonZero(e ast.Expr) bool {
	r, ok := f.Range(e)
	if !ok {
		return false
	}
	return !point(zero).Within(r) || f.excluded(e, f.root, zero)
}

// An Overflow is an operation or conversion that may wrap around.
type Overflow struct {
	Expr  ast.Expr   // the operation or conversion
	Type  types.Type // its type
	Range Interval   // its mathematical value, which may exceed Type
}

// Overflows returns the integer operations and conversions in e (including
// e itself) whose wraparound may make e's value differ from its
// mathematical value, innermost first. For example, int32(c) truncates if
// c may exceed int32, and c+d wraps if the sum may.
//
// Wraparound that cannot change e's value is not reported: in int32
// arithmetic, c+2*d is exact if its mathematical value fits in int32, even
// if 2*d wraps, because + and * are exact modulo 2^32.
//
// Calls are opaque: their arguments are not examined. To check the
// arguments of ssa.MakeValAndOff(int32(c), off), ask about each one.
func (f *Facts) Overflows(e ast.Expr) []Overflow { return f.overflows(e, inf) }

// OverflowsMod is like Overflows, but reports only wraparound that may make
// e's value differ from its mathematical value modulo 2^bits. An auxint
// for a 32-bit operation, such as ADDLconst's [-c], need only be right
// modulo 2^32; one for a 64-bit operation, modulo 2^64.
func (f *Facts) OverflowsMod(e ast.Expr, bits uint) []Overflow { return f.overflows(e, bits) }

// Exact reports whether integer expression e's value is provably the
// mathematical value of its expression: no operation or conversion in it
// wraps around in a way that changes its value.
func (f *Facts) Exact(e ast.Expr) bool { return len(f.Overflows(e)) == 0 }

func (f *Facts) overflows(e ast.Expr, need uint) []Overflow {
	if f.store.bottom {
		return nil
	}
	var out []Overflow
	f.check(e, f.root, need, func(o Overflow) { out = append(out, o) })
	return out
}

// Expression structure.

func unparen(e ast.Expr) ast.Expr {
	for {
		p, ok := e.(*ast.ParenExpr)
		if !ok {
			return e
		}
		e = p.X
	}
}

func (f *Facts) typeOf(e ast.Expr, en *env) types.Type {
	if tv, ok := en.info.Types[e]; ok {
		return tv.Type
	}
	if id, ok := e.(*ast.Ident); ok {
		if obj := en.info.Defs[id]; obj != nil {
			return obj.Type()
		}
		if obj := en.info.Uses[id]; obj != nil {
			return obj.Type()
		}
	}
	return nil
}

func (f *Facts) constOf(e ast.Expr, en *env) (*big.Int, bool) {
	tv, ok := en.info.Types[e]
	if !ok || tv.Value == nil {
		return nil, false
	}
	v := constant.ToInt(tv.Value)
	if v.Kind() != constant.Int {
		return nil, false
	}
	return new(big.Int).SetString(v.ExactString(), 10)
}

// conversion returns x if e is an integer-to-integer conversion T(x).
func (f *Facts) conversion(e ast.Expr, en *env) (ast.Expr, bool) {
	call, ok := e.(*ast.CallExpr)
	if !ok || len(call.Args) != 1 || call.Ellipsis.IsValid() {
		return nil, false
	}
	tv, ok := en.info.Types[call.Fun]
	if !ok || !tv.IsType() || !isInt(tv.Type) || !isInt(f.typeOf(call.Args[0], en)) {
		return nil, false
	}
	return call.Args[0], true
}

func (f *Facts) obj(id *ast.Ident, en *env) types.Object {
	if obj := en.info.Uses[id]; obj != nil {
		return obj
	}
	return en.info.Defs[id]
}

// bound returns what identifier e stands for, if it is an inlined
// helper's parameter or local variable.
func (f *Facts) bound(e ast.Expr, en *env) (binding, bool) {
	id, ok := e.(*ast.Ident)
	if !ok || en.bind == nil {
		return binding{}, false
	}
	b, ok := en.bind[f.obj(id, en)]
	return b, ok
}

var arith = map[token.Token]bool{
	token.ADD: true, token.SUB: true, token.MUL: true, token.QUO: true, token.REM: true,
	token.AND: true, token.OR: true, token.XOR: true, token.AND_NOT: true,
	token.SHL: true, token.SHR: true,
}

// computes reports whether e is an integer operation or conversion,
// whose value may wrap around.
func (f *Facts) computes(e ast.Expr, en *env) bool {
	e = unparen(e)
	if _, ok := f.constOf(e, en); ok || !isInt(f.typeOf(e, en)) {
		return false
	}
	switch x := e.(type) {
	case *ast.BinaryExpr:
		return arith[x.Op]
	case *ast.UnaryExpr:
		return x.Op == token.SUB || x.Op == token.XOR || x.Op == token.ADD
	}
	_, ok := f.conversion(e, en)
	return ok
}

// Keys name expressions in the fact store. A go key names an
// expression's Go value. A math key names its mathematical value: it
// omits integer conversions, so int64(c)+int64(d) and c+d share one.
// An inlined helper's parameters are named by their arguments' go keys.
func (f *Facts) key(e ast.Expr, en *env, math bool) string {
	e = unparen(e)
	if c, ok := f.constOf(e, en); ok {
		return c.String()
	}
	if b, ok := f.bound(e, en); ok {
		k := f.key(b.e, b.en, false)
		if math {
			// The mathematical value of a parameter is the Go value
			// of its argument, which is not the argument's mathematical
			// value.
			k = "go" + k
		}
		return k
	}
	if x, ok := f.conversion(e, en); ok {
		if math {
			return f.key(x, en, true)
		}
		return types.TypeString(f.typeOf(e, en), nil) + "(" + f.key(x, en, false) + ")"
	}
	if tv, ok := en.info.Types[e]; ok && tv.IsType() {
		return types.TypeString(tv.Type, nil)
	}
	switch x := e.(type) {
	case *ast.Ident:
		obj := f.obj(x, en)
		if obj != nil && obj.Pkg() != nil && obj.Parent() == obj.Pkg().Scope() {
			return obj.Pkg().Path() + "." + x.Name
		}
		return x.Name
	case *ast.SelectorExpr:
		if id, ok := x.X.(*ast.Ident); ok {
			if pn, ok := f.obj(id, en).(*types.PkgName); ok {
				return pn.Imported().Path() + "." + x.Sel.Name
			}
		}
		return f.key(x.X, en, false) + "." + x.Sel.Name
	case *ast.CallExpr:
		s := f.key(x.Fun, en, false) + "("
		for i, a := range x.Args {
			if i > 0 {
				s += ","
			}
			s += f.key(a, en, false)
		}
		return s + ")"
	case *ast.IndexExpr:
		return f.key(x.X, en, false) + "[" + f.key(x.Index, en, false) + "]"
	case *ast.StarExpr:
		return "*" + f.key(x.X, en, false)
	case *ast.UnaryExpr:
		return x.Op.String() + "(" + f.key(x.X, en, math && x.Op != token.NOT) + ")"
	case *ast.BinaryExpr:
		m := math && arith[x.Op]
		y := f.key(x.Y, en, m && x.Op != token.SHL && x.Op != token.SHR) // shifts use the count's Go value
		return "(" + f.key(x.X, en, m) + x.Op.String() + y + ")"
	}
	// Unique: no facts are shared with other expressions.
	return fmt.Sprintf("?%p/%p", e, en)
}

// Evaluation.

// goRange returns the possible Go values of e.
func (f *Facts) goRange(e ast.Expr, en *env) (Interval, bool) {
	e = unparen(e)
	r, ok := f.goRangeNoMath(e, en)
	if !ok {
		return r, false
	}
	if f.exact(e, en) {
		r = meet(r, f.mathRange(e, en))
	} else if t := f.typeOf(e, en); fixedWidth(t) && f.check(e, en, width(t), func(Overflow) {}) {
		r = meet(r, f.ringRange(e, en, t, 0))
	}
	return r, true
}

// ringRange returns the possible values of e's mathematical value
// modulo 2^w, as a value of t, which is w bits wide: the ring fact about
// e, or what its operands' ring ranges imply if e is a sum or difference
// that does not wrap. So int32(c+16) is in [16, 31] if uint32(c) < 16.
func (f *Facts) ringRange(e ast.Expr, en *env, t types.Type, depth int) Interval {
	e = unparen(e)
	tr, _ := TypeRange(t)
	r := f.store.get(ringKey(t)+f.key(e, en, true), tr)
	if depth > 8 || !isInt(f.typeOf(e, en)) {
		return r
	}
	if c, ok := f.constOf(e, en); ok {
		tb, _ := basicInt(t)
		return meet(r, point(wrapTo(c, bits(tb), unsigned(tb))))
	}
	if !f.computes(e, en) {
		// Its mathematical value is its Go value.
		if gr, ok := f.goRange(e, en); ok && gr.Within(tr) {
			r = meet(r, gr)
		}
		return r
	}
	if x, ok := f.conversion(e, en); ok {
		return meet(r, f.ringRange(x, en, t, depth+1))
	}
	if b, ok := e.(*ast.BinaryExpr); ok && (b.Op == token.ADD || b.Op == token.SUB) {
		x := f.ringRange(b.X, en, t, depth+1)
		y := f.ringRange(b.Y, en, t, depth+1)
		if s := binop(b.Op, x, y); s.Within(tr) {
			r = meet(r, s)
		}
	}
	return r
}

// goRangeNoMath is goRange without using facts about e's mathematical value.
func (f *Facts) goRangeNoMath(e ast.Expr, en *env) (Interval, bool) {
	t := f.typeOf(e, en)
	if !isInt(t) {
		return Interval{}, false
	}
	if c, ok := f.constOf(e, en); ok {
		return point(c), true
	}
	tr, _ := TypeRange(t)
	r := f.store.get("g:"+f.key(e, en, false), tr)
	if b, ok := f.bound(e, en); ok {
		br, _ := f.goRange(b.e, b.en)
		return meet(r, br), true
	}
	// clip uses res, the mathematical result of e's operation on its
	// operands' Go values, if it cannot have wrapped around.
	clip := func(res Interval) Interval {
		if sr, _ := safeRange(t); res.Within(sr) {
			return meet(r, res)
		}
		return r
	}
	if x, ok := f.conversion(e, en); ok {
		xr, _ := f.goRange(x, en)
		return f.trimImages(clip(xr), x, en, t), true
	}
	switch x := e.(type) {
	case *ast.BinaryExpr:
		if !arith[x.Op] {
			return r, true
		}
		a, _ := f.goRange(x.X, en)
		b, _ := f.goRange(x.Y, en)
		return clip(binop(x.Op, a, b)), true
	case *ast.UnaryExpr:
		a, _ := f.goRange(x.X, en)
		if res, ok := unop(x.Op, a); ok {
			return clip(res), true
		}
	case *ast.CallExpr:
		if res, ok := f.callRange(x, en); ok {
			return clip(res), true
		}
	}
	return r, true
}

// trimImages narrows r, the range of t(x), by the values excluded for x:
// if the conversion is injective, t(x) is not the image of any of them.
func (f *Facts) trimImages(r Interval, x ast.Expr, en *env, t types.Type) Interval {
	xt := f.typeOf(x, en)
	if !injective(xt, t) || f.store.bottom {
		return r
	}
	ne := f.store.m["g:"+f.key(x, en, false)].ne
	if len(ne) == 0 {
		return r
	}
	tb, _ := basicInt(t)
	w := bits(tb)
	for changed := true; changed && !r.Empty(); {
		changed = false
		for _, v := range ne {
			img := wrapTo(v, w, unsigned(tb))
			if r.Lo != nil && r.Lo.Cmp(img) == 0 {
				r.Lo, changed = add(img, one), true
			}
			if r.Hi != nil && r.Hi.Cmp(img) == 0 {
				r.Hi, changed = sub(img, one), true
			}
		}
	}
	return r
}

// wrapTo returns x reduced modulo 2^w to the range of a w-bit integer.
func wrapTo(x *big.Int, w uint, unsigned bool) *big.Int {
	m := bigPow2(w)
	y := new(big.Int).Mod(x, m)
	if !unsigned && y.Bit(int(w)-1) == 1 {
		y.Sub(y, m)
	}
	return y
}

// mathRange returns the possible mathematical values of e: its value
// if its operations and conversions were on unbounded integers.
// Operations other than arithmetic and integer conversions, such as
// calls, are the same as in Go.
func (f *Facts) mathRange(e ast.Expr, en *env) Interval {
	e = unparen(e)
	if !isInt(f.typeOf(e, en)) {
		return full
	}
	if c, ok := f.constOf(e, en); ok {
		return point(c)
	}
	r := f.store.get("m:"+f.key(e, en, true), full)
	if !f.computes(e, en) {
		gr, _ := f.goRangeNoMath(e, en)
		return meet(r, gr)
	}
	if x, ok := f.conversion(e, en); ok {
		return meet(r, f.mathRange(x, en))
	}
	switch x := e.(type) {
	case *ast.BinaryExpr:
		a := f.mathRange(x.X, en)
		var b Interval
		if x.Op == token.SHL || x.Op == token.SHR {
			b, _ = f.goRange(x.Y, en)
		} else {
			b = f.mathRange(x.Y, en)
		}
		return meet(r, binop(x.Op, a, b))
	case *ast.UnaryExpr:
		if res, ok := unop(x.Op, f.mathRange(x.X, en)); ok {
			return meet(r, res)
		}
	}
	return r
}

// inf is an unbounded congruence width: equality.
const inf = ^uint(0)

// width returns the bits of integer type t's values that are the same
// on every host: 32 for int, uint, and uintptr.
func width(t types.Type) uint {
	b, ok := basicInt(t)
	if !ok {
		return 0
	}
	if w := bits(b); w != 0 {
		return w
	}
	return 32
}

// check reports the operations and conversions in e that may keep e's Go
// value from being congruent to its mathematical value modulo 2^need
// (equal to it, if need is inf), and reports whether there are none.
//
// Consider an operation of type T, which is w bits wide, on operands
// whose Go values are congruent to their mathematical values modulo 2^w.
// If the operation is +, -, *, <<, &, |, ^, &^, unary - or ^, or an
// integer conversion, the result is too, because these operations
// commute with reduction modulo 2^w. (Other operations, such as / and >>,
// need exact operands.) If need ≤ w, that is enough. Otherwise, the
// result must also not wrap: its mathematical value must be in T, or
// else congruent modulo 2^need to a value in T (see ringRange).
func (f *Facts) check(e ast.Expr, en *env, need uint, report func(Overflow)) bool {
	e = unparen(e)
	if !f.computes(e, en) {
		return true
	}
	t := f.typeOf(e, en)
	w := width(t)
	var operands []ast.Expr
	ring := true
	if x, ok := f.conversion(e, en); ok {
		operands = []ast.Expr{x}
	} else {
		switch x := e.(type) {
		case *ast.BinaryExpr:
			operands = []ast.Expr{x.X}
			if x.Op != token.SHL && x.Op != token.SHR {
				// A shift's count is used as is.
				operands = append(operands, x.Y)
			}
			ring = x.Op != token.QUO && x.Op != token.REM && x.Op != token.SHR
		case *ast.UnaryExpr:
			operands = []ast.Expr{x.X}
		}
	}
	operandNeed := inf
	if ring {
		operandNeed = min(need, w)
	}
	ok := true
	for _, x := range operands {
		ok = f.check(x, en, operandNeed, report) && ok
	}
	if need > w {
		sr, _ := safeRange(t)
		mr := f.mathRange(e, en)
		if !mr.Within(sr) && !(fixedWidth(t) && f.ringWithin(e, en, need, sr)) {
			report(Overflow{Expr: e, Type: t, Range: mr})
			ok = false
		}
	}
	return ok
}

// fixedWidth reports whether integer type t has the same width on every
// host, so that it holds exactly one value of each residue modulo 2^width(t).
func fixedWidth(t types.Type) bool {
	b, ok := basicInt(t)
	return ok && bits(b) != 0
}

// exact reports whether e's Go value is its mathematical value.
func (f *Facts) exact(e ast.Expr, en *env) bool {
	return f.check(e, en, inf, func(Overflow) {})
}

// Ring facts record facts about inexact expressions. Suppose e has a
// fixed-width type T, w bits wide, and its Go value is congruent to its
// mathematical value modulo 2^w. Then ringKey(T)+mathKey records the range
// of e's Go value. Any expression with the same mathematical value, a type
// of the same width and signedness, and the same congruence has the same
// Go value, since such a type holds just one value of each residue.
//
// For example, from is32Bit(int64(off)+int64(scale)*2), with off an int32
// and scale an int64, the int64 off+int32(scale)*2 is in [-2^31, 2^31-1]
// and congruent to off+scale*2 modulo 2^64.
func ringKey(t types.Type) string {
	b, _ := basicInt(t)
	s := "s"
	if unsigned(b) {
		s = "u"
	}
	return "r" + strconv.FormatUint(uint64(bits(b)), 10) + s + ":"
}

// ringWithin reports whether a ring fact shows that e's mathematical value
// is congruent modulo 2^need to a value in iv.
func (f *Facts) ringWithin(e ast.Expr, en *env, need uint, iv Interval) bool {
	for _, t := range []types.Type{types.Typ[types.Int64], types.Typ[types.Uint64], types.Typ[types.Int32],
		types.Typ[types.Uint32], types.Typ[types.Int16], types.Typ[types.Uint16], types.Typ[types.Int8], types.Typ[types.Uint8]} {
		if width(t) != need {
			continue
		}
		if f.store.get(ringKey(t)+f.key(e, en, true), full).Within(iv) {
			return true
		}
	}
	return false
}

func binop(op token.Token, a, b Interval) Interval {
	switch op {
	case token.ADD:
		return addIv(a, b)
	case token.SUB:
		return subIv(a, b)
	case token.MUL:
		return mulIv(a, b)
	case token.QUO:
		return quoIv(a, b)
	case token.REM:
		return remIv(a, b)
	case token.AND:
		return andIv(a, b)
	case token.OR:
		return orIv(a, b)
	case token.XOR:
		return xorIv(a, b)
	case token.AND_NOT:
		return andNotIv(a, b)
	case token.SHL:
		return shlIv(a, b)
	case token.SHR:
		return shrIv(a, b)
	}
	return full
}

func unop(op token.Token, a Interval) (Interval, bool) {
	switch op {
	case token.ADD:
		return a, true
	case token.SUB:
		return negIv(a), true
	case token.XOR:
		// ^x == -x-1 in two's complement.
		return negIv(a).shift(big.NewInt(-1)), true
	}
	return full, false
}

// excluded reports whether Go value x is known not to be e's value.
func (f *Facts) excluded(e ast.Expr, en *env, x *big.Int) bool {
	e = unparen(e)
	if slices.ContainsFunc(f.store.m["g:"+f.key(e, en, false)].ne, func(y *big.Int) bool { return x.Cmp(y) == 0 }) {
		return true
	}
	if b, ok := f.bound(e, en); ok {
		return f.excluded(b.e, b.en, x)
	}
	// An injective conversion is 0 only if its operand is.
	if y, ok := f.conversion(e, en); ok && x.Sign() == 0 && injective(f.typeOf(y, en), f.typeOf(e, en)) {
		return f.excluded(y, en, x)
	}
	return false
}
