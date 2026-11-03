package facts

import (
	"errors"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math/big"
	mbits "math/bits"
)

func isBool(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	return ok && b.Info()&types.IsBoolean != 0
}

// wrapBits reduces x modulo 2^w into the signed or unsigned w-bit range.
func wrapBits(x *big.Int, w uint, signed bool) *big.Int {
	m := bigPow2(w)
	r := new(big.Int).Mod(x, m)
	if signed && r.Cmp(bigPow2(w-1)) >= 0 {
		r.Sub(r, m)
	}
	return r
}

// interp evaluates rule expressions with Go semantics (on a 64-bit host),
// or with mathematical semantics, in which integer operations and
// conversions do not wrap.
type interp struct {
	f    *Facts
	vals map[types.Object]any
}

var errUnknown = errors.New("cannot evaluate")

func (in *interp) wrap(x *big.Int, t types.Type) (*big.Int, error) {
	b, ok := basicInt(t)
	if !ok {
		return nil, errUnknown
	}
	w := bits(b)
	if w == 0 {
		w = 64
	}
	return wrapBits(x, w, !unsigned(b)), nil
}

func (in *interp) eval(e ast.Expr, en *env, math bool) (any, error) {
	f := in.f
	e = unparen(e)
	if tv, ok := en.info.Types[e]; ok && tv.Value != nil {
		switch tv.Value.Kind() {
		case constant.Bool:
			return constant.BoolVal(tv.Value), nil
		case constant.Int:
			c, _ := f.constOf(e, en)
			return c, nil
		}
		return nil, errUnknown
	}
	if b, ok := f.bound(e, en); ok {
		return in.eval(b.e, b.en, false)
	}
	t := f.typeOf(e, en)
	result := func(x *big.Int) (any, error) {
		if math {
			return x, nil
		}
		return in.wrap(x, t)
	}
	if x, ok := f.conversion(e, en); ok {
		v, err := in.eval(x, en, math)
		if err != nil {
			return nil, err
		}
		return result(v.(*big.Int))
	}
	switch x := e.(type) {
	case *ast.Ident:
		if v, ok := in.vals[f.obj(x, en)]; ok {
			return v, nil
		}
	case *ast.UnaryExpr:
		v, err := in.eval(x.X, en, math)
		if err != nil {
			return nil, err
		}
		switch x.Op {
		case token.NOT:
			return !v.(bool), nil
		case token.SUB:
			return result(new(big.Int).Neg(v.(*big.Int)))
		case token.XOR:
			return result(new(big.Int).Not(v.(*big.Int)))
		case token.ADD:
			return result(v.(*big.Int))
		}
	case *ast.BinaryExpr:
		if x.Op == token.LAND || x.Op == token.LOR {
			l, err := in.eval(x.X, en, false)
			if err != nil {
				return nil, err
			}
			if l.(bool) == (x.Op == token.LOR) {
				return l, nil
			}
			return in.eval(x.Y, en, false)
		}
		if isComparison(x.Op) {
			l, err1 := in.eval(x.X, en, false)
			r, err2 := in.eval(x.Y, en, false)
			if err1 != nil || err2 != nil {
				return nil, errUnknown
			}
			if lb, ok := l.(bool); ok {
				switch x.Op {
				case token.EQL:
					return lb == r.(bool), nil
				case token.NEQ:
					return lb != r.(bool), nil
				}
				return nil, errUnknown
			}
			li, ok1 := l.(*big.Int)
			ri, ok2 := r.(*big.Int)
			if !ok1 || !ok2 {
				return nil, errUnknown
			}
			c := li.Cmp(ri)
			switch x.Op {
			case token.EQL:
				return c == 0, nil
			case token.NEQ:
				return c != 0, nil
			case token.LSS:
				return c < 0, nil
			case token.LEQ:
				return c <= 0, nil
			case token.GTR:
				return c > 0, nil
			case token.GEQ:
				return c >= 0, nil
			}
		}
		if !arith[x.Op] {
			break
		}
		l, err := in.eval(x.X, en, math)
		if err != nil {
			return nil, err
		}
		shift := x.Op == token.SHL || x.Op == token.SHR
		r, err := in.eval(x.Y, en, math && !shift)
		if err != nil {
			return nil, err
		}
		a, b := l.(*big.Int), r.(*big.Int)
		z := new(big.Int)
		switch x.Op {
		case token.ADD:
			z.Add(a, b)
		case token.SUB:
			z.Sub(a, b)
		case token.MUL:
			z.Mul(a, b)
		case token.QUO, token.REM:
			if b.Sign() == 0 {
				return nil, errUnknown // panics
			}
			if x.Op == token.QUO {
				z.Quo(a, b)
			} else {
				z.Rem(a, b)
			}
		case token.AND:
			z.And(a, b)
		case token.OR:
			z.Or(a, b)
		case token.XOR:
			z.Xor(a, b)
		case token.AND_NOT:
			z.AndNot(a, b)
		case token.SHL, token.SHR:
			if b.Sign() < 0 {
				return nil, errUnknown // panics
			}
			s := uint(200)
			if b.IsUint64() && b.Uint64() < 200 {
				s = uint(b.Uint64())
			} else if math && x.Op == token.SHL && a.Sign() != 0 {
				return nil, errUnknown
			}
			if x.Op == token.SHL {
				z.Lsh(a, s)
			} else {
				z.Rsh(a, s)
			}
		}
		return result(z)
	case *ast.CallExpr:
		if id, ok := unparen(x.Fun).(*ast.Ident); ok {
			if b, ok := f.obj(id, en).(*types.Builtin); ok && (b.Name() == "min" || b.Name() == "max") {
				var m *big.Int
				for _, a := range x.Args {
					v, err := in.eval(a, en, false)
					if err != nil {
						return nil, err
					}
					vi := v.(*big.Int)
					if m == nil || (b.Name() == "min") == (vi.Cmp(m) < 0) {
						m = vi
					}
				}
				return m, nil
			}
		}
		if fn, _, _, ok := f.callee(x, en); ok && fn.Pkg() != nil && fn.Pkg().Path() == "math/bits" && len(x.Args) == 1 {
			v, err := in.eval(x.Args[0], en, false)
			if err != nil {
				return nil, err
			}
			return bitsFunc(fn.Name(), v.(*big.Int).Uint64())
		}
		if body, ben, ok := f.inline(x, en); ok {
			return in.eval(body, ben, false)
		}
	}
	return nil, errUnknown
}

func bitsFunc(name string, u uint64) (any, error) {
	var r int
	switch name {
	case "Len", "Len64":
		r = mbits.Len64(u)
	case "Len32":
		r = mbits.Len32(uint32(u))
	case "Len16":
		r = mbits.Len16(uint16(u))
	case "Len8":
		r = mbits.Len8(uint8(u))
	case "TrailingZeros", "TrailingZeros64":
		r = mbits.TrailingZeros64(u)
	case "TrailingZeros32":
		r = mbits.TrailingZeros32(uint32(u))
	case "TrailingZeros16":
		r = mbits.TrailingZeros16(uint16(u))
	case "TrailingZeros8":
		r = mbits.TrailingZeros8(uint8(u))
	case "LeadingZeros", "LeadingZeros64":
		r = mbits.LeadingZeros64(u)
	case "LeadingZeros32":
		r = mbits.LeadingZeros32(uint32(u))
	case "LeadingZeros16":
		r = mbits.LeadingZeros16(uint16(u))
	case "LeadingZeros8":
		r = mbits.LeadingZeros8(uint8(u))
	case "OnesCount", "OnesCount64":
		r = mbits.OnesCount64(u)
	case "OnesCount32":
		r = mbits.OnesCount32(uint32(u))
	case "OnesCount16":
		r = mbits.OnesCount16(uint16(u))
	case "OnesCount8":
		r = mbits.OnesCount8(uint8(u))
	default:
		return nil, errUnknown
	}
	return big.NewInt(int64(r)), nil
}

// Eval returns the value of expression e of the rule, with Go semantics,
// given vals, values of the rule's variables (*big.Int for integers, bool
// for booleans). It reports false if e cannot be evaluated: it uses a
// variable not in vals, calls a function that is not understood, or
// panics.
func (f *Facts) Eval(e ast.Expr, vals map[types.Object]any) (any, bool) {
	in := &interp{f: f, vals: vals}
	v, err := in.eval(e, f.root, false)
	return v, err == nil
}

// Holds reports whether vals, values of the rule's integer variables,
// are a witness to what f assumes: the condition holds, each AssumeNot
// condition is false, each AssumeVar and AssumeIn range holds, and no
// variable has an ExcludeVar value.
//
// A part of a condition that cannot be evaluated but does not depend on
// vals, such as x.Uses == 1 or clobber(x), is assumed to be what the
// condition needs. A part that does depend on vals but cannot be
// evaluated, such as a call to a helper with loops, makes Holds false.
func (f *Facts) Holds(vals map[types.Object]any) bool {
	in := &interp{f: f, vals: vals}
	if f.cond != nil {
		if t := in.truth(f.cond, f.root); t != tTrue && t != tFree {
			return false
		}
	}
	for _, a := range f.nots {
		want := tTrue
		if !a.truth {
			want = tFalse
		}
		if in.truth(a.e, a.en) != want {
			return false
		}
	}
	for name, iv := range f.vars {
		if f.tr == nil || f.tr.Vars[name] == nil {
			return false
		}
		x, ok := vals[f.tr.Vars[name]].(*big.Int)
		if !ok || !point(x).Within(iv) {
			return false
		}
	}
	for _, x := range f.excl {
		if f.tr == nil || f.tr.Vars[x.name] == nil {
			return false
		}
		v, ok := vals[f.tr.Vars[x.name]].(*big.Int)
		if !ok || v.Cmp(x.x) == 0 {
			return false
		}
	}
	for _, w := range f.ins {
		v, err := in.eval(w.e, f.root, false)
		x, ok := v.(*big.Int)
		if err != nil || !ok || !point(x).Within(w.iv) {
			return false
		}
	}
	return true
}

// A truth is the value of a condition: true, false, free (unknown, but
// independent of the variables' values), or unknown.
type truth int8

const (
	tFalse truth = iota
	tTrue
	tFree
	tUnknown
)

// truth evaluates boolean expression e in Kleene's three-valued logic,
// distinguishing unknowns that depend on in.vals.
func (in *interp) truth(e ast.Expr, en *env) truth {
	e = unparen(e)
	switch x := e.(type) {
	case *ast.UnaryExpr:
		if x.Op == token.NOT {
			switch t := in.truth(x.X, en); t {
			case tTrue:
				return tFalse
			case tFalse:
				return tTrue
			default:
				return t
			}
		}
	case *ast.BinaryExpr:
		if x.Op == token.LAND || x.Op == token.LOR {
			l, r := in.truth(x.X, en), in.truth(x.Y, en)
			absorb, ident := tFalse, tTrue
			if x.Op == token.LOR {
				absorb, ident = tTrue, tFalse
			}
			switch {
			case l == absorb || r == absorb:
				return absorb
			case l == tUnknown || r == tUnknown:
				return tUnknown
			case l == tFree || r == tFree:
				return tFree
			}
			return ident
		}
	}
	if v, err := in.eval(e, en, false); err == nil {
		if b, ok := v.(bool); ok {
			if b {
				return tTrue
			}
			return tFalse
		}
	}
	if in.depends(e, en) {
		return tUnknown
	}
	return tFree
}

// depends reports whether e refers to a variable in in.vals.
func (in *interp) depends(e ast.Expr, en *env) bool {
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		id, ok := n.(*ast.Ident)
		if !ok || found {
			return !found
		}
		if b, ok := in.f.bound(id, en); ok {
			found = in.depends(b.e, b.en)
			return !found
		}
		if _, ok := in.vals[in.f.obj(id, en)]; ok {
			found = true
		}
		return !found
	})
	return found
}
