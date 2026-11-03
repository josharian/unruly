package term

import (
	"go/ast"
	"go/constant"
	"go/token"
	"strings"
)

// Facts are what is known about the symbols of some terms: their
// structure and the conditions assumed to hold.
type Facts struct {
	terms  map[string]*Term    // compound terms by symbol
	known  map[string]bool     // canonical conditions assumed true
	neg    map[string]bool     // canonical conditions assumed false
	bounds map[string]interval // integer bounds on symbols

	helpers map[string]helper // see UseHelpers
}

// interval is an inclusive integer range; nil ends are unbounded.
type interval struct{ lo, hi constant.Value }

// NewFacts returns an empty set of facts.
func NewFacts() *Facts {
	return &Facts{
		terms:  map[string]*Term{},
		known:  map[string]bool{},
		neg:    map[string]bool{},
		bounds: map[string]interval{},
	}
}

// Clone returns a copy of f.
func (f *Facts) Clone() *Facts {
	g := NewFacts()
	for k, v := range f.terms {
		g.terms[k] = v
	}
	for k, v := range f.known {
		g.known[k] = v
	}
	for k, v := range f.neg {
		g.neg[k] = v
	}
	for k, v := range f.bounds {
		g.bounds[k] = v
	}
	g.helpers = f.helpers
	return g
}

// AddTerm records the structure of t and its subterms.
func (f *Facts) AddTerm(t *Term) {
	if t.Op == nil || f.terms[t.Sym] == t {
		return
	}
	f.terms[t.Sym] = t
	for _, a := range t.Args {
		f.AddTerm(a)
	}
}

// Term returns the compound term with symbol sym, or nil.
func (f *Facts) Term(sym string) *Term { return f.terms[sym] }

// Assume records that the conjuncts of cond hold.
func (f *Facts) Assume(cond string) {
	for _, c := range Conjuncts(cond) {
		f.known[c] = true
		x := unparen(parse(c))
		if u, ok := x.(*ast.UnaryExpr); ok && u.Op == token.NOT {
			f.neg[format(unparen(u.X))] = true
		}
		if sym, op, k, ok := comparison(x); ok {
			f.bounds[sym] = f.bounds[sym].meet(op, k)
		}
	}
}

func unparen(x ast.Expr) ast.Expr {
	for {
		p, ok := x.(*ast.ParenExpr)
		if !ok {
			return x
		}
		x = p.X
	}
}

// Implies reports whether c, a Go boolean expression over symbols,
// certainly holds given f.
func (f *Facts) Implies(c string) bool {
	c = Canon(c)
	if f.known[c] {
		return true
	}
	x := unparen(parse(c))
	if x == nil {
		return false
	}
	switch x := x.(type) {
	case *ast.BinaryExpr:
		switch x.Op {
		case token.LAND:
			return f.Implies(format(x.X)) && f.Implies(format(x.Y))
		case token.LOR:
			return f.Implies(format(x.X)) || f.Implies(format(x.Y))
		}
	case *ast.UnaryExpr:
		if x.Op == token.NOT {
			return f.Refutes(format(x.X))
		}
	case *ast.CallExpr:
		if alwaysTrue(x) {
			return true
		}
	}
	if v := f.eval(c); v != nil && v.Kind() == constant.Bool {
		return constant.BoolVal(v)
	}
	if v, ok := f.opTest(x); ok {
		return v
	}
	if sym, op, k, ok := comparison(x); ok {
		return f.bounds[sym].implies(op, k)
	}
	return false
}

// Refutes reports whether c certainly does not hold given f.
func (f *Facts) Refutes(c string) bool {
	c = Canon(c)
	if f.neg[c] {
		return true
	}
	x := unparen(parse(c))
	if x == nil {
		return false
	}
	switch x := x.(type) {
	case *ast.BinaryExpr:
		switch x.Op {
		case token.LAND:
			return f.Refutes(format(x.X)) || f.Refutes(format(x.Y))
		case token.LOR:
			return f.Refutes(format(x.X)) && f.Refutes(format(x.Y))
		case token.LSS, token.GTR:
			// a < b refutes b < a.
			if f.known[format(&ast.BinaryExpr{X: x.Y, Op: x.Op, Y: x.X})] {
				return true
			}
		}
	case *ast.UnaryExpr:
		if x.Op == token.NOT {
			return f.Implies(format(x.X))
		}
	case *ast.CallExpr:
		if f.exclusive(x) {
			return true
		}
	}
	if v := f.eval(c); v != nil && v.Kind() == constant.Bool {
		return !constant.BoolVal(v)
	}
	if v, ok := f.opTest(x); ok {
		return !v
	}
	if sym, op, k, ok := comparison(x); ok {
		return f.bounds[sym].refutes(op, k)
	}
	return false
}

// alwaysTrue reports whether x calls a rule helper that always returns
// true. These are defined in cmd/compile/internal/ssa/rewrite.go:
// Clobber, ClobberIfDead, CountRule, and NoteRule each end in
// "return true" with no other return. (Older trees spell them in lower
// case.)
func alwaysTrue(x *ast.CallExpr) bool {
	switch funcName(x.Fun) {
	case "Clobber", "clobber", "ClobberIfDead", "clobberIfDead",
		"CountRule", "countRule", "NoteRule", "noteRule":
		return true
	}
	return false
}

func funcName(x ast.Expr) string {
	switch x := x.(type) {
	case *ast.Ident:
		return x.Name
	case *ast.SelectorExpr:
		return x.Sel.Name
	}
	return ""
}

// opTest evaluates x.Op == OpFoo or x.Op != OpFoo for a symbol x with
// known structure.
func (f *Facts) opTest(x ast.Expr) (bool, bool) {
	b, ok := x.(*ast.BinaryExpr)
	if !ok || b.Op != token.EQL && b.Op != token.NEQ {
		return false, false
	}
	l, r := b.X, b.Y
	sel, ok := l.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Op" {
		l, r = r, l
		sel, ok = l.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "Op" {
			return false, false
		}
	}
	id, ok := sel.X.(*ast.Ident)
	if !ok {
		return false, false
	}
	t := f.terms[id.Name]
	if t == nil {
		return false, false
	}
	name := funcName(r)
	if !strings.HasPrefix(name, "Op") {
		return false, false
	}
	eq := name == "Op"+t.Op.QualifiedName()
	return eq == (b.Op == token.EQL), true
}

// comparison decomposes x as sym op k, for a symbol sym and integer
// constant k.
func comparison(x ast.Expr) (sym string, op token.Token, k constant.Value, ok bool) {
	b, ok := x.(*ast.BinaryExpr)
	if !ok {
		return "", 0, nil, false
	}
	switch b.Op {
	case token.LSS, token.LEQ, token.GTR, token.GEQ, token.EQL, token.NEQ:
	default:
		return "", 0, nil, false
	}
	l, r, op := unparen(b.X), unparen(b.Y), b.Op
	if _, isID := l.(*ast.Ident); !isID {
		l, r = r, l
		op = flip(op)
	}
	id, isID := l.(*ast.Ident)
	if !isID {
		return "", 0, nil, false
	}
	k = Eval(format(r))
	if k == nil || k.Kind() != constant.Int {
		return "", 0, nil, false
	}
	if Eval(id.Name) != nil {
		return "", 0, nil, false // true, false, iota...
	}
	return id.Name, op, k, true
}

func flip(op token.Token) token.Token {
	switch op {
	case token.LSS:
		return token.GTR
	case token.LEQ:
		return token.GEQ
	case token.GTR:
		return token.LSS
	case token.GEQ:
		return token.LEQ
	}
	return op
}

var one = constant.MakeInt64(1)

func lt(a, b constant.Value) bool { return constant.Compare(a, token.LSS, b) }

// meet narrows i by the fact (x op k).
func (i interval) meet(op token.Token, k constant.Value) interval {
	lower := func(v constant.Value) {
		if i.lo == nil || lt(i.lo, v) {
			i.lo = v
		}
	}
	upper := func(v constant.Value) {
		if i.hi == nil || lt(v, i.hi) {
			i.hi = v
		}
	}
	switch op {
	case token.LSS:
		upper(constant.BinaryOp(k, token.SUB, one))
	case token.LEQ:
		upper(k)
	case token.GTR:
		lower(constant.BinaryOp(k, token.ADD, one))
	case token.GEQ:
		lower(k)
	case token.EQL:
		lower(k)
		upper(k)
	}
	return i
}

// implies reports whether every x in i satisfies x op k.
func (i interval) implies(op token.Token, k constant.Value) bool {
	switch op {
	case token.LSS:
		return i.hi != nil && lt(i.hi, k)
	case token.LEQ:
		return i.hi != nil && !lt(k, i.hi)
	case token.GTR:
		return i.lo != nil && lt(k, i.lo)
	case token.GEQ:
		return i.lo != nil && !lt(i.lo, k)
	case token.EQL:
		return i.lo != nil && i.hi != nil && constant.Compare(i.lo, token.EQL, k) && constant.Compare(i.hi, token.EQL, k)
	case token.NEQ:
		return i.hi != nil && lt(i.hi, k) || i.lo != nil && lt(k, i.lo)
	}
	return false
}

// refutes reports whether no x in i satisfies x op k.
func (i interval) refutes(op token.Token, k constant.Value) bool {
	switch op {
	case token.LSS:
		return i.lo != nil && !lt(i.lo, k)
	case token.LEQ:
		return i.lo != nil && lt(k, i.lo)
	case token.GTR:
		return i.hi != nil && !lt(k, i.hi)
	case token.GEQ:
		return i.hi != nil && lt(i.hi, k)
	case token.EQL:
		return i.lo != nil && lt(k, i.lo) || i.hi != nil && lt(i.hi, k)
	case token.NEQ:
		return i.implies(token.EQL, k)
	}
	return false
}

// exclusive reports whether call x contradicts a known call. The pairs
// come from the helpers in cmd/compile/internal/ssa/rewrite.go:
//
//   - CanonLessThan is a strict order, so CanonLessThan(x, y) and
//     CanonLessThan(y, x) can't both hold.
//   - IsSamePtr(p1, p2) means p1 and p2 are the same address, and
//     Disjoint1(p1, n1, p2, n2) that the n1 bytes at p1 and the n2 bytes
//     at p2 don't overlap. Disjoint1 is false for p1 == p2 when the sizes
//     are nonzero; it can be true for the same address only if
//     DisjointTypes rules out aliasing, which can't happen for two
//     correctly typed pointers to the same memory. Rules apply Disjoint1
//     to the sizes of nonempty moves.
func (f *Facts) exclusive(x *ast.CallExpr) bool {
	knownAny := func(names []string, args ...ast.Expr) bool {
		for _, n := range names {
			c := &ast.CallExpr{Fun: renameFunc(x.Fun, n), Args: args}
			if f.known[format(c)] {
				return true
			}
		}
		return false
	}
	a := x.Args
	switch funcName(x.Fun) {
	case "CanonLessThan", "canonLessThan":
		if len(a) == 2 {
			return knownAny([]string{funcName(x.Fun)}, a[1], a[0])
		}
	case "Disjoint1", "disjoint":
		if len(a) == 4 {
			return knownAny([]string{"IsSamePtr", "isSamePtr"}, a[0], a[2]) ||
				knownAny([]string{"IsSamePtr", "isSamePtr"}, a[2], a[0])
		}
	case "IsSamePtr", "isSamePtr":
		if len(a) == 2 {
			for k := range f.known {
				c, ok := unparen(parse(k)).(*ast.CallExpr)
				if !ok || len(c.Args) != 4 {
					continue
				}
				if n := funcName(c.Fun); n != "Disjoint1" && n != "disjoint" {
					continue
				}
				p1, p2 := format(c.Args[0]), format(c.Args[2])
				x1, x2 := format(a[0]), format(a[1])
				if p1 == x1 && p2 == x2 || p1 == x2 && p2 == x1 {
					return true
				}
			}
		}
	}
	return false
}

// renameFunc returns function expression fun with its name replaced,
// keeping any package qualifier.
func renameFunc(fun ast.Expr, name string) ast.Expr {
	if sel, ok := fun.(*ast.SelectorExpr); ok {
		return &ast.SelectorExpr{X: sel.X, Sel: ast.NewIdent(name)}
	}
	return ast.NewIdent(name)
}
