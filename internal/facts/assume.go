package facts

import (
	"go/ast"
	"go/token"
	"go/types"
	"math/big"
	"slices"
)

// A store maps keys (see Facts.key) to what is known about them:
// "g:"+key for an expression's Go value, "m:"+key for its mathematical value.
type store struct {
	m       map[string]fact
	changed bool
	bottom  bool // the facts are contradictory
}

type fact struct {
	iv Interval
	ne []*big.Int // values excluded by !=
}

// get returns the interval known for k, met with base and
// narrowed by excluded endpoints.
func (s *store) get(k string, base Interval) Interval {
	ft, ok := s.m[k]
	if !ok {
		return base
	}
	iv := meet(base, ft.iv)
	for changed := true; changed && !iv.Empty(); {
		changed = false
		for _, x := range ft.ne {
			if iv.Lo != nil && iv.Lo.Cmp(x) == 0 {
				iv.Lo, changed = add(x, one), true
			}
			if iv.Hi != nil && iv.Hi.Cmp(x) == 0 {
				iv.Hi, changed = sub(x, one), true
			}
		}
	}
	return iv
}

func (s *store) meet(k string, iv Interval) {
	ft := s.m[k]
	n := meet(ft.iv, iv)
	if n.equal(ft.iv) {
		return
	}
	ft.iv = n
	s.m[k] = ft
	s.changed = true
	if s.get(k, full).Empty() {
		s.bottom = true
	}
}

func (s *store) exclude(k string, x *big.Int) {
	ft := s.m[k]
	if slices.ContainsFunc(ft.ne, func(y *big.Int) bool { return x.Cmp(y) == 0 }) {
		return
	}
	ft.ne = append(slices.Clip(ft.ne), x)
	s.m[k] = ft
	s.changed = true
	if s.get(k, full).Empty() {
		s.bottom = true
	}
}

func (s *store) clone() store {
	c := store{m: make(map[string]fact, len(s.m)), bottom: s.bottom}
	for k, v := range s.m {
		c.m[k] = v
	}
	return c
}

// assume records the facts implied by boolean expression e having value truth.
func (f *Facts) assume(e ast.Expr, en *env, truth bool) {
	e = unparen(e)
	switch x := e.(type) {
	case *ast.UnaryExpr:
		if x.Op == token.NOT {
			f.assume(x.X, en, !truth)
		}
	case *ast.BinaryExpr:
		switch {
		case x.Op == token.LAND && truth, x.Op == token.LOR && !truth:
			f.assume(x.X, en, truth)
			f.assume(x.Y, en, truth)
		case x.Op == token.LOR && truth:
			// x.Y is evaluated only if x.X is false.
			f.either(func() { f.assume(x.X, en, true) }, func() {
				f.assume(x.X, en, false)
				f.assume(x.Y, en, true)
			})
		case x.Op == token.LAND && !truth:
			f.either(func() { f.assume(x.X, en, false) }, func() {
				f.assume(x.X, en, true)
				f.assume(x.Y, en, false)
			})
		case x.Op.IsOperator() && isComparison(x.Op):
			op := x.Op
			if !truth {
				op = negate[op]
			}
			f.compare(x.X, op, x.Y, en)
		}
	case *ast.Ident:
		if b, ok := f.bound(x, en); ok {
			f.assume(b.e, b.en, truth)
		}
	case *ast.CallExpr:
		if body, ben, ok := f.inline(x, en); ok {
			f.assume(body, ben, truth)
		}
	}
}

// either records the facts common to the alternatives.
func (f *Facts) either(alts ...func()) {
	orig := f.store
	var outs []store
	for _, alt := range alts {
		f.store = orig.clone()
		alt()
		if !f.store.bottom {
			outs = append(outs, f.store)
		}
	}
	f.store = orig
	if len(outs) == 0 {
		f.store.bottom = true
		return
	}
	for k := range outs[0].m {
		iv := outs[0].get(k, full)
		ne := outs[0].m[k].ne
		in := true
		for _, o := range outs[1:] {
			ft, ok := o.m[k]
			if !ok {
				in = false
				break
			}
			iv = hull(iv, o.get(k, full))
			ne = slices.DeleteFunc(slices.Clone(ne), func(x *big.Int) bool {
				return !slices.ContainsFunc(ft.ne, func(y *big.Int) bool { return x.Cmp(y) == 0 })
			})
		}
		if !in {
			continue
		}
		f.store.meet(k, iv)
		for _, x := range ne {
			f.store.exclude(k, x)
		}
	}
}

func isComparison(op token.Token) bool {
	_, ok := negate[op]
	return ok
}

var negate = map[token.Token]token.Token{
	token.EQL: token.NEQ, token.NEQ: token.EQL,
	token.LSS: token.GEQ, token.GEQ: token.LSS,
	token.GTR: token.LEQ, token.LEQ: token.GTR,
}

// compare records the facts implied by l op r.
func (f *Facts) compare(l ast.Expr, op token.Token, r ast.Expr, en *env) {
	lr, lok := f.goRange(l, en)
	rr, rok := f.goRange(r, en)
	if !lok || !rok {
		return
	}
	below := func(iv Interval, d int64) Interval { // (-inf, iv.Hi+d]
		if iv.Hi == nil {
			return full
		}
		return Interval{Hi: add(iv.Hi, big.NewInt(d))}
	}
	above := func(iv Interval, d int64) Interval { // [iv.Lo+d, +inf)
		if iv.Lo == nil {
			return full
		}
		return Interval{Lo: add(iv.Lo, big.NewInt(d))}
	}
	f.relate(l, op, r, en)
	switch op {
	case token.EQL:
		f.constrain(l, en, rr)
		f.constrain(r, en, lr)
	case token.NEQ:
		if c, ok := rr.isPoint(); ok {
			f.exclude(l, en, c)
		}
		if c, ok := lr.isPoint(); ok {
			f.exclude(r, en, c)
		}
	case token.LSS:
		f.constrain(l, en, below(rr, -1))
		f.constrain(r, en, above(lr, 1))
	case token.LEQ:
		f.constrain(l, en, below(rr, 0))
		f.constrain(r, en, above(lr, 0))
	case token.GTR:
		f.constrain(l, en, above(rr, 1))
		f.constrain(r, en, below(lr, -1))
	case token.GEQ:
		f.constrain(l, en, above(rr, 0))
		f.constrain(r, en, below(lr, 0))
	}
}

// relate records the sign of the mathematical differences of l and r
// that l op r implies, if l and r are exact: l < r means r-l ≥ 1.
// Differences of variables are thus bounded, as c-d in
// (BTQconst [c] (SHLQconst [d] x)) && c > d => (BTQconst [c-d] x).
func (f *Facts) relate(l ast.Expr, op token.Token, r ast.Expr, en *env) {
	if _, ok := f.constOf(l, en); ok {
		return
	}
	if _, ok := f.constOf(r, en); ok {
		return
	}
	if !isInt(f.typeOf(l, en)) || !isInt(f.typeOf(r, en)) || !f.exact(l, en) || !f.exact(r, en) {
		return
	}
	kl, kr := f.key(l, en, true), f.key(r, en, true)
	lr := "m:(" + kl + "-" + kr + ")" // l-r
	rl := "m:(" + kr + "-" + kl + ")" // r-l
	// l < r (l <= r) means r-l ≥ d; l > r (l >= r) means l-r ≥ d.
	var d int64
	switch op {
	case token.LSS, token.GTR:
		d = 1
	case token.LEQ, token.GEQ:
		d = 0
	case token.EQL:
		f.store.meet(lr, point(zero))
		f.store.meet(rl, point(zero))
		return
	default:
		return
	}
	if op == token.GTR || op == token.GEQ {
		lr, rl = rl, lr
	}
	f.store.meet(rl, Interval{Lo: big.NewInt(d)})
	f.store.meet(lr, Interval{Hi: big.NewInt(-d)})
}

// constrain records that e's Go value lies in iv.
func (f *Facts) constrain(e ast.Expr, en *env, iv Interval) {
	e = unparen(e)
	if _, ok := f.constOf(e, en); ok || !isInt(f.typeOf(e, en)) {
		return
	}
	if b, ok := f.bound(e, en); ok {
		f.constrain(b.e, b.en, iv)
		return
	}
	f.store.meet("g:"+f.key(e, en, false), iv)
	if x, ok := f.conversion(e, en); ok {
		xt, et := f.typeOf(x, en), f.typeOf(e, en)
		if p, ok := preimage(iv, xt, et); ok {
			f.constrain(x, en, p)
			// The preimage of an interval that omits an end of e's
			// type need not be an interval: uint64(c) > 0 for an
			// int32 c means c != 0. Exclude such ends.
			tr, _ := TypeRange(et)
			for _, end := range []*big.Int{tr.Lo, tr.Hi} {
				if point(end).Within(iv) {
					continue
				}
				if pe, ok := preimage(point(end), xt, et); ok {
					if px, ok := pe.isPoint(); ok {
						f.exclude(x, en, px)
					}
				}
			}
		}
	}
	if !f.computes(e, en) {
		return
	}
	if f.exact(e, en) {
		f.constrainMath(e, en, iv)
		return
	}
	if t := f.typeOf(e, en); fixedWidth(t) && f.check(e, en, width(t), func(Overflow) {}) {
		k := f.key(e, en, true)
		f.store.meet(ringKey(t)+k, iv)
		// The same residues, in the type of the other signedness.
		if o, oiv, ok := otherSign(t, iv); ok {
			f.store.meet(ringKey(o)+k, oiv)
		}
	}
}

// otherSign returns the type of fixed-width type t's width and the other
// signedness, and the values of that type with the same residues as iv's,
// if they form an interval.
func otherSign(t types.Type, iv Interval) (types.Type, Interval, bool) {
	b, ok := basicInt(t)
	if !ok || bits(b) == 0 {
		return nil, Interval{}, false
	}
	w := bits(b)
	var o types.Type
	for _, k := range []types.BasicKind{types.Int8, types.Int16, types.Int32, types.Int64, types.Uint8, types.Uint16, types.Uint32, types.Uint64} {
		ob := types.Typ[k]
		if bits(ob) == w && unsigned(ob) != unsigned(b) {
			o = ob
		}
	}
	tr, _ := TypeRange(t)
	or, _ := TypeRange(o)
	iv = meet(iv, tr)
	if iv.Empty() || !iv.Bounded() {
		return nil, Interval{}, false
	}
	m := bigPow2(w)
	for _, s := range []*big.Int{zero, m, new(big.Int).Neg(m)} {
		if c := iv.shift(s); c.Within(or) {
			return o, c, true
		}
	}
	return nil, Interval{}, false
}

// constrainMath records that e's mathematical value lies in iv.
func (f *Facts) constrainMath(e ast.Expr, en *env, iv Interval) {
	e = unparen(e)
	if _, ok := f.constOf(e, en); ok || !isInt(f.typeOf(e, en)) {
		return
	}
	if !f.computes(e, en) {
		// Its mathematical value is its Go value.
		if b, ok := f.bound(e, en); ok {
			f.constrain(b.e, b.en, iv)
		} else {
			f.store.meet("g:"+f.key(e, en, false), iv)
		}
		return
	}
	f.store.meet("m:"+f.key(e, en, true), iv)
	if x, ok := f.conversion(e, en); ok {
		f.constrainMath(x, en, iv)
		return
	}
	switch x := e.(type) {
	case *ast.UnaryExpr:
		if x.Op == token.SUB {
			f.constrainMath(x.X, en, negIv(iv))
		}
	case *ast.BinaryExpr:
		if x.Op != token.ADD && x.Op != token.SUB {
			return
		}
		if c, ok := f.constOf(x.Y, en); ok {
			if x.Op == token.ADD {
				c = new(big.Int).Neg(c)
			}
			f.constrainMath(x.X, en, iv.shift(c)) // x + c ∈ iv ⇒ x ∈ iv - c
		} else if c, ok := f.constOf(x.X, en); ok {
			if x.Op == token.ADD {
				f.constrainMath(x.Y, en, iv.shift(new(big.Int).Neg(c))) // c + y ∈ iv ⇒ y ∈ iv - c
			} else {
				f.constrainMath(x.Y, en, negIv(iv).shift(c)) // c - y ∈ iv ⇒ y ∈ c - iv
			}
		}
	}
}

// exclude records that e's Go value is not x.
func (f *Facts) exclude(e ast.Expr, en *env, x *big.Int) {
	e = unparen(e)
	if _, ok := f.constOf(e, en); ok || !isInt(f.typeOf(e, en)) {
		return
	}
	if b, ok := f.bound(e, en); ok {
		f.exclude(b.e, b.en, x)
		return
	}
	f.store.exclude("g:"+f.key(e, en, false), x)
	if y, ok := f.conversion(e, en); ok {
		if p, ok := preimage(point(x), f.typeOf(y, en), f.typeOf(e, en)); ok {
			if px, ok := p.isPoint(); ok {
				f.exclude(y, en, px)
			}
		}
	}
}

// injective reports whether converting from integer type s to t
// preserves distinctness on every host.
func injective(s, t types.Type) bool {
	sb, ok1 := basicInt(s)
	tb, ok2 := basicInt(t)
	return ok1 && ok2 && bits(sb) != 0 && bits(tb) >= bits(sb)
}

// preimage returns the values x of type s such that t(x) ∈ iv,
// if the conversion is injective.
func preimage(iv Interval, s, t types.Type) (Interval, bool) {
	if !injective(s, t) {
		return Interval{}, false
	}
	sr, _ := TypeRange(s)
	tr, _ := TypeRange(t)
	tb, _ := basicInt(t)
	m := bigPow2(bits(tb))
	// Values of s in t's range convert to themselves. Others are out of
	// range by less than 2^bits(t), and wrap around once.
	p := meet(meet(iv, tr), sr)
	below := meet(meet(iv.shift(new(big.Int).Neg(m)), sr), Interval{Hi: sub(tr.Lo, one)})
	above := meet(meet(iv.shift(m), sr), Interval{Lo: add(tr.Hi, one)})
	return hull(hull(p, below), above), true
}
