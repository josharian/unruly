package facts

import (
	"fmt"
	"go/types"
	"math/big"
)

// An Interval is a closed range of integers [Lo, Hi].
// A nil bound is unbounded. Lo > Hi means the interval is empty.
// Intervals are values: their big.Ints are never modified.
type Interval struct {
	Lo, Hi *big.Int
}

// Range returns the interval [lo, hi].
func Range(lo, hi int64) Interval { return Interval{big.NewInt(lo), big.NewInt(hi)} }

// Bounded reports whether both ends of iv are finite.
func (iv Interval) Bounded() bool { return iv.Lo != nil && iv.Hi != nil }

// Empty reports whether iv contains no integers.
func (iv Interval) Empty() bool { return iv.Bounded() && iv.Lo.Cmp(iv.Hi) > 0 }

// Within reports whether iv ⊆ o. The empty interval is within every interval.
func (iv Interval) Within(o Interval) bool {
	if iv.Empty() {
		return true
	}
	if o.Lo != nil && (iv.Lo == nil || iv.Lo.Cmp(o.Lo) < 0) {
		return false
	}
	if o.Hi != nil && (iv.Hi == nil || iv.Hi.Cmp(o.Hi) > 0) {
		return false
	}
	return true
}

// Contains reports whether x ∈ iv.
func (iv Interval) Contains(x int64) bool { return point(big.NewInt(x)).Within(iv) }

func (iv Interval) String() string {
	if iv.Empty() {
		return "[]"
	}
	lo, hi := "-inf", "+inf"
	if iv.Lo != nil {
		lo = iv.Lo.String()
	}
	if iv.Hi != nil {
		hi = iv.Hi.String()
	}
	if iv.Lo != nil && iv.Hi != nil && iv.Lo.Cmp(iv.Hi) == 0 {
		return "[" + lo + "]"
	}
	return fmt.Sprintf("[%s, %s]", lo, hi)
}

func (iv Interval) equal(o Interval) bool {
	return eqBound(iv.Lo, o.Lo) && eqBound(iv.Hi, o.Hi)
}

func eqBound(a, b *big.Int) bool {
	if a == nil || b == nil {
		return a == b
	}
	return a.Cmp(b) == 0
}

// isPoint returns the single member of iv, if it has exactly one.
func (iv Interval) isPoint() (*big.Int, bool) {
	if iv.Bounded() && iv.Lo.Cmp(iv.Hi) == 0 {
		return iv.Lo, true
	}
	return nil, false
}

var (
	full = Interval{}
	zero = big.NewInt(0)
	one  = big.NewInt(1)
)

func point(x *big.Int) Interval { return Interval{x, x} }

func bigPow2(n uint) *big.Int { return new(big.Int).Lsh(one, n) }

func add(a, b *big.Int) *big.Int { return new(big.Int).Add(a, b) }
func sub(a, b *big.Int) *big.Int { return new(big.Int).Sub(a, b) }

// nonneg reports whether every member of iv is ≥ 0.
func (iv Interval) nonneg() bool { return iv.Lo != nil && iv.Lo.Sign() >= 0 }

func meet(a, b Interval) Interval {
	r := a
	if b.Lo != nil && (r.Lo == nil || b.Lo.Cmp(r.Lo) > 0) {
		r.Lo = b.Lo
	}
	if b.Hi != nil && (r.Hi == nil || b.Hi.Cmp(r.Hi) < 0) {
		r.Hi = b.Hi
	}
	return r
}

// hull returns the smallest interval containing a and b.
func hull(a, b Interval) Interval {
	if a.Empty() {
		return b
	}
	if b.Empty() {
		return a
	}
	var r Interval
	if a.Lo != nil && b.Lo != nil {
		r.Lo = minBig(a.Lo, b.Lo)
	}
	if a.Hi != nil && b.Hi != nil {
		r.Hi = maxBig(a.Hi, b.Hi)
	}
	return r
}

func minBig(a, b *big.Int) *big.Int {
	if a.Cmp(b) <= 0 {
		return a
	}
	return b
}

func maxBig(a, b *big.Int) *big.Int {
	if a.Cmp(b) >= 0 {
		return a
	}
	return b
}

// shift returns iv + k.
func (iv Interval) shift(k *big.Int) Interval {
	var r Interval
	if iv.Lo != nil {
		r.Lo = add(iv.Lo, k)
	}
	if iv.Hi != nil {
		r.Hi = add(iv.Hi, k)
	}
	return r
}

func addIv(a, b Interval) Interval {
	var r Interval
	if a.Lo != nil && b.Lo != nil {
		r.Lo = add(a.Lo, b.Lo)
	}
	if a.Hi != nil && b.Hi != nil {
		r.Hi = add(a.Hi, b.Hi)
	}
	return r
}

func negIv(a Interval) Interval {
	var r Interval
	if a.Hi != nil {
		r.Lo = new(big.Int).Neg(a.Hi)
	}
	if a.Lo != nil {
		r.Hi = new(big.Int).Neg(a.Lo)
	}
	return r
}

func subIv(a, b Interval) Interval { return addIv(a, negIv(b)) }

// corners returns the hull of f applied to the corners of a × b,
// which is the range of f over a × b when f is monotonic in each argument.
// a and b must be bounded and non-empty.
func corners(a, b Interval, f func(x, y *big.Int) *big.Int) Interval {
	var r Interval
	for _, x := range []*big.Int{a.Lo, a.Hi} {
		for _, y := range []*big.Int{b.Lo, b.Hi} {
			v := f(x, y)
			if r.Lo == nil {
				r = point(v)
				continue
			}
			r.Lo, r.Hi = minBig(r.Lo, v), maxBig(r.Hi, v)
		}
	}
	return r
}

func mulIv(a, b Interval) Interval {
	if !a.Bounded() || !b.Bounded() || a.Empty() || b.Empty() {
		return full
	}
	return corners(a, b, func(x, y *big.Int) *big.Int { return new(big.Int).Mul(x, y) })
}

// nonzero removes 0 from the ends of a divisor's interval:
// division by zero panics, so it produces no value.
func nonzero(b Interval) Interval {
	if b.Lo != nil && b.Lo.Sign() == 0 {
		b.Lo = one
	}
	if b.Hi != nil && b.Hi.Sign() == 0 {
		b.Hi = big.NewInt(-1)
	}
	return b
}

// absMax returns max |x| for x in a, or nil if unbounded.
func absMax(a Interval) *big.Int {
	if !a.Bounded() {
		return nil
	}
	return maxBig(new(big.Int).Abs(a.Lo), new(big.Int).Abs(a.Hi))
}

// quoIv is Go's truncated division.
func quoIv(a, b Interval) Interval {
	b = nonzero(b)
	if a.Empty() || b.Empty() {
		return Interval{one, zero}
	}
	if b.Lo != nil && b.Lo.Sign() < 0 && (b.Hi == nil || b.Hi.Sign() > 0) {
		// b spans 0: |a/b| ≤ |a|.
		m := absMax(a)
		if m == nil {
			return full
		}
		return Interval{new(big.Int).Neg(m), m}
	}
	if !a.Bounded() {
		return full
	}
	// b has one sign; a/b is monotonic in each argument.
	// An unbounded end of b acts as ±infinity, where a/b is 0.
	quo := func(x, y *big.Int) *big.Int {
		if y == nil {
			return new(big.Int)
		}
		return new(big.Int).Quo(x, y)
	}
	var r Interval
	for _, x := range []*big.Int{a.Lo, a.Hi} {
		for _, y := range []*big.Int{b.Lo, b.Hi} {
			v := quo(x, y)
			if r.Lo == nil {
				r = point(v)
				continue
			}
			r.Lo, r.Hi = minBig(r.Lo, v), maxBig(r.Hi, v)
		}
	}
	return r
}

// remIv is Go's truncated remainder, whose sign is the dividend's.
func remIv(a, b Interval) Interval {
	b = nonzero(b)
	if a.Empty() || b.Empty() {
		return Interval{one, zero}
	}
	r := full
	if m := absMax(b); m != nil {
		m = sub(m, one)
		r = Interval{new(big.Int).Neg(m), m}
	}
	if m := absMax(a); m != nil {
		r = meet(r, Interval{new(big.Int).Neg(m), m})
	}
	if a.nonneg() {
		r = meet(r, Interval{Lo: zero})
	}
	if a.Hi != nil && a.Hi.Sign() <= 0 {
		r = meet(r, Interval{Hi: zero})
	}
	return r
}

// maxShift bounds shift counts: for |x| < 2^65, x>>s for s ≥ maxShift is
// the same as for maxShift, and x<<s for larger s is not computed.
const maxShift = 128

// shlIv is a << s, computed without wraparound. A negative count panics
// in Go, so it produces no value.
func shlIv(a, s Interval) Interval {
	s = meet(s, Interval{Lo: zero})
	if !a.Bounded() || !s.Bounded() || a.Empty() || s.Empty() || s.Hi.Cmp(big.NewInt(maxShift)) > 0 {
		return full
	}
	return corners(a, s, func(x, y *big.Int) *big.Int { return new(big.Int).Lsh(x, uint(y.Uint64())) })
}

// shrIv is a >> s: floor(a / 2^s), which is both Go's arithmetic shift of
// signed values and its logical shift of unsigned ones.
func shrIv(a, s Interval) Interval {
	s = meet(s, Interval{Lo: zero})
	if s.Empty() {
		return Interval{one, zero}
	}
	lim := big.NewInt(maxShift)
	if s.Hi == nil || s.Hi.Cmp(lim) > 0 {
		s.Hi = lim
	}
	if s.Lo.Cmp(lim) > 0 {
		s.Lo = lim
	}
	if !a.Bounded() {
		// Shifting right moves toward 0 (or -1).
		var r Interval
		if a.nonneg() {
			r.Lo = zero
		}
		if a.Hi != nil && a.Hi.Sign() < 0 {
			r.Hi = big.NewInt(-1)
		}
		if a.Lo != nil && a.Lo.Sign() < 0 {
			r.Lo = a.Lo
		}
		if a.Hi != nil && a.Hi.Sign() >= 0 {
			r.Hi = a.Hi
		}
		return r
	}
	return corners(a, s, func(x, y *big.Int) *big.Int { return new(big.Int).Rsh(x, uint(y.Uint64())) })
}

// allOnes returns 2^bitlen(x) - 1 for x ≥ 0: the largest value with no
// bits above x's highest bit.
func allOnes(x *big.Int) *big.Int { return sub(bigPow2(uint(x.BitLen())), one) }

func andIv(a, b Interval) Interval {
	switch {
	case a.nonneg() && b.nonneg():
		r := Interval{Lo: zero, Hi: a.Hi}
		if r.Hi == nil || b.Hi != nil && b.Hi.Cmp(r.Hi) < 0 {
			r.Hi = b.Hi
		}
		return r
	case a.nonneg():
		return Interval{Lo: zero, Hi: a.Hi}
	case b.nonneg():
		return Interval{Lo: zero, Hi: b.Hi}
	}
	return bitwise(a, b)
}

func orIv(a, b Interval) Interval {
	if !a.nonneg() || !b.nonneg() {
		return bitwise(a, b)
	}
	r := Interval{Lo: maxBig(a.Lo, b.Lo)}
	if a.Hi != nil && b.Hi != nil {
		r.Hi = allOnes(maxBig(a.Hi, b.Hi))
	}
	return r
}

func xorIv(a, b Interval) Interval {
	if !a.nonneg() || !b.nonneg() {
		return bitwise(a, b)
	}
	r := Interval{Lo: zero}
	if a.Hi != nil && b.Hi != nil {
		r.Hi = allOnes(maxBig(a.Hi, b.Hi))
	}
	return r
}

func andNotIv(a, b Interval) Interval {
	if a.nonneg() {
		return Interval{Lo: zero, Hi: a.Hi}
	}
	return bitwise(a, b)
}

// bitwise bounds a bitwise operation on a and b: if both are k-bit two's
// complement numbers, so is the result.
func bitwise(a, b Interval) Interval {
	if !a.Bounded() || !b.Bounded() {
		return full
	}
	k := 0
	for _, x := range []*big.Int{a.Lo, a.Hi, b.Lo, b.Hi} {
		if x.Sign() < 0 {
			x = new(big.Int).Not(x) // -x-1
		}
		k = max(k, x.BitLen()+1)
	}
	return rangeOfWidth(uint(k), false)
}

// Integer types.

func basicInt(t types.Type) (*types.Basic, bool) {
	if t == nil {
		return nil, false
	}
	b, ok := t.Underlying().(*types.Basic)
	if !ok || b.Info()&types.IsInteger == 0 {
		return nil, false
	}
	return b, true
}

// isInt reports whether t is an integer type (not a type parameter).
func isInt(t types.Type) bool {
	_, ok := basicInt(t)
	return ok
}

// bits returns the width of integer type b. Int, uint, and uintptr are
// 32 or 64 bits, depending on the compiler's host; bits returns 0 for them.
func bits(b *types.Basic) uint {
	switch b.Kind() {
	case types.Int8, types.Uint8:
		return 8
	case types.Int16, types.Uint16:
		return 16
	case types.Int32, types.Uint32:
		return 32
	case types.Int64, types.Uint64, types.UntypedInt, types.UntypedRune:
		return 64
	}
	return 0
}

func rangeOfWidth(w uint, unsigned bool) Interval {
	if unsigned {
		return Interval{zero, sub(bigPow2(w), one)}
	}
	return Interval{new(big.Int).Neg(bigPow2(w - 1)), sub(bigPow2(w-1), one)}
}

func unsigned(b *types.Basic) bool { return b.Info()&types.IsUnsigned != 0 }

// TypeRange returns the values that integer type t can hold, and false
// if t is not an integer type. Int, uint, and uintptr hold 64 bits,
// the most they hold on any host.
func TypeRange(t types.Type) (Interval, bool) {
	b, ok := basicInt(t)
	if !ok {
		return Interval{}, false
	}
	w := bits(b)
	if w == 0 {
		w = 64
	}
	return rangeOfWidth(w, unsigned(b)), true
}

// safeRange returns the values that integer type t holds on every host:
// those that can be stored in t without wraparound. It differs from
// TypeRange for int, uint, and uintptr, which may be 32 bits.
func safeRange(t types.Type) (Interval, bool) {
	b, ok := basicInt(t)
	if !ok {
		return Interval{}, false
	}
	w := bits(b)
	if w == 0 {
		w = 32
	}
	return rangeOfWidth(w, unsigned(b)), true
}
