package gensem

import (
	"fmt"
	"math"
	"math/bits"
	"strconv"
)

// The semantics of generic ops follow the op comments in
// cmd/compile/internal/ssa/_gen/genericOps.go. Where an op's result is
// undefined for some inputs because its producer promises they do not
// occur (a bounded shift by too much, Avg64u with arg0 < arg1),
// evaluating it returns *Undefined. Where its result is valid but
// machine-dependent (a division by zero, an out-of-range float-to-int
// conversion), it returns *Unspecified.

// GenericOps returns the semantics of the generic ops, keyed by op name.
// The map is fresh, so callers may add arch ops to it.
func GenericOps() map[string]OpFunc {
	m := make(map[string]OpFunc, len(genericOps))
	for k, f := range genericOps {
		m[k] = f
	}
	return m
}

var genericOps = buildGeneric()

func undef(in *OpInput, format string, args ...any) error {
	return &Undefined{in.V.OpName(), fmt.Sprintf(format, args...)}
}

func illTyped(in *OpInput, format string, args ...any) error {
	return &IllTyped{in.V.OpName(), fmt.Sprintf(format, args...)}
}

// intArg returns arg i, which must be an integer at least w bits wide
// (any width if w is 0), as a w-bit integer.
//
// SSA is weakly typed: a wider value stands for its low bits (rules
// compute Div16 with Div32 of extended args, typed as the 16-bit result),
// and on most machines a narrower value lives in a register whose upper
// bits are unspecified. An op reading a narrower value as wider sees
// garbage upper bits, chosen by Interp.Garbage.
func intArg(in *OpInput, i, w int) (Val, error) {
	x := in.Args[i]
	if x.Kind != KInt {
		want := "integer"
		if w != 0 {
			want = fmt.Sprintf("%d-bit integer", w)
		}
		return Val{}, illTyped(in, "arg%d is %s, want %s", i, describe(x), want)
	}
	if w == 0 || x.Width == w {
		return x, nil
	}
	if x.Width > w {
		return IntVal(w, x.Bits), nil
	}
	junk := splitmix(in.Garbage ^ x.Bits ^ uint64(x.Width)<<56)
	return IntVal(w, x.Bits|junk&^mask(x.Width)), nil
}

func splitmix(x uint64) uint64 {
	x += 0x9e3779b97f4a7c15
	x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9
	x = (x ^ (x >> 27)) * 0x94d049bb133111eb
	return x ^ (x >> 31)
}

func floatArg(in *OpInput, i, w int) (Val, error) {
	x := in.Args[i]
	if x.Kind != KFloat || x.Width != w {
		return Val{}, illTyped(in, "arg%d is %s, want float%d", i, describe(x), w)
	}
	return x, nil
}

func boolArg(in *OpInput, i int) (Val, error) {
	x := in.Args[i]
	if x.Kind != KBool {
		return Val{}, illTyped(in, "arg%d is %s, want bool", i, describe(x))
	}
	return x, nil
}

// ptrArg returns arg i as a pointer. An integer stands for an address
// (rules compare pointer-typed integer constants with EqPtr).
func ptrArg(in *OpInput, i int) (Val, error) {
	w := int(in.Cfg.PtrSize * 8)
	x := in.Args[i]
	switch x.Kind {
	case KPtr:
		return PtrVal(w, x.Base, x.Bits), nil
	case KInt:
		v, err := intArg(in, i, w)
		return PtrVal(w, 0, v.Bits), err
	}
	return Val{}, illTyped(in, "arg%d is %s, want a pointer", i, describe(x))
}

func flagsArg(in *OpInput, i int) (Val, error) {
	x := in.Args[i]
	if x.Kind != KFlags {
		return Val{}, illTyped(in, "arg%d is %s, want flags", i, describe(x))
	}
	return x, nil
}

func describe(x Val) string {
	switch x.Kind {
	case KInt:
		return fmt.Sprintf("a %d-bit integer", x.Width)
	case KFloat:
		return fmt.Sprintf("a float%d", x.Width)
	case KBool:
		return "a bool"
	case KFlags:
		return "flags"
	case KTuple:
		return "a tuple"
	case KPtr:
		return "a pointer"
	case KMem:
		return "memory"
	}
	return "invalid"
}

// typeWidth returns the width in bits of v's type, which must be an integer type.
func typeWidth(in *OpInput) (int, error) {
	t := in.V.Type
	if t == nil || !(t.IsInteger() || t.IsPtr()) || t.Size == 0 {
		return 0, illTyped(in, "result type %v is not an integer type", t)
	}
	return t.Bits(), nil
}

func ints2(in *OpInput, w int) (a, b Val, err error) {
	if a, err = intArg(in, 0, w); err != nil {
		return
	}
	b, err = intArg(in, 1, w)
	return
}

func buildGeneric() map[string]OpFunc {
	m := map[string]OpFunc{}
	for _, w := range []int{8, 16, 32, 64} {
		w := w
		ws := strconv.Itoa(w)
		bin := func(name string, f func(a, b uint64) uint64) {
			m[name+ws] = func(in *OpInput) (Val, error) {
				a, b, err := ints2(in, w)
				if err != nil {
					return Val{}, err
				}
				return IntVal(w, f(a.Bits, b.Bits)), nil
			}
		}
		bin("Add", func(a, b uint64) uint64 { return a + b })
		bin("Sub", func(a, b uint64) uint64 { return a - b })
		bin("Mul", func(a, b uint64) uint64 { return a * b })
		bin("And", func(a, b uint64) uint64 { return a & b })
		bin("Or", func(a, b uint64) uint64 { return a | b })
		bin("Xor", func(a, b uint64) uint64 { return a ^ b })
		un := func(name string, f func(a uint64) uint64) {
			m[name+ws] = func(in *OpInput) (Val, error) {
				a, err := intArg(in, 0, w)
				if err != nil {
					return Val{}, err
				}
				return IntVal(w, f(a.Bits)), nil
			}
		}
		un("Neg", func(a uint64) uint64 { return -a })
		un("Com", func(a uint64) uint64 { return ^a })
		if w >= 16 {
			un("Bswap", func(a uint64) uint64 { return bits.ReverseBytes64(a) >> (64 - w) })
		}
		un("BitRev", func(a uint64) uint64 { return bits.Reverse64(a) >> (64 - w) })

		m["Const"+ws] = func(in *OpInput) (Val, error) { return IntVal(w, uint64(in.V.AuxInt)), nil }

		// Counting ops: the result's width comes from its type (int).
		count := func(name string, nonZero bool, f func(a uint64) int) {
			m[name] = func(in *OpInput) (Val, error) {
				a, err := intArg(in, 0, w)
				if err != nil {
					return Val{}, err
				}
				if nonZero && a.Bits == 0 {
					return Val{}, undef(in, "arg is zero")
				}
				rw, err := typeWidth(in)
				if err != nil {
					return Val{}, err
				}
				return IntVal(rw, uint64(f(a.Bits))), nil
			}
		}
		ctz := func(a uint64) int { return min(bits.TrailingZeros64(a), w) }
		count("Ctz"+ws, false, ctz)
		count("Ctz"+ws+"NonZero", true, ctz)
		count("BitLen"+ws, false, bits.Len64)
		count("PopCount"+ws, false, bits.OnesCount64)

		m["RotateLeft"+ws] = func(in *OpInput) (Val, error) {
			a, err := intArg(in, 0, w)
			if err != nil {
				return Val{}, err
			}
			k, err := intArg(in, 1, 0)
			if err != nil {
				return Val{}, err
			}
			s := uint(k.Bits) & uint(w-1)
			return IntVal(w, a.Bits<<s|a.Bits>>(uint(w)-s)), nil
		}

		for _, unsigned := range []bool{false, true} {
			unsigned := unsigned
			suffix := ""
			if unsigned {
				suffix = "u"
			}
			for _, isMod := range []bool{false, true} {
				isMod := isMod
				name := "Div"
				if isMod {
					name = "Mod"
				}
				m[name+ws+suffix] = func(in *OpInput) (Val, error) { return divmod(in, w, unsigned, isMod) }
			}
			mm := func(name string, wantMin bool) {
				m[name+ws+suffix] = func(in *OpInput) (Val, error) {
					a, b, err := ints2(in, w)
					if err != nil {
						return Val{}, err
					}
					less := a.Int() < b.Int()
					if unsigned {
						less = a.Bits < b.Bits
					}
					if less == wantMin {
						return a, nil
					}
					return b, nil
				}
			}
			mm("Min", true)
			mm("Max", false)
		}

		cmp := func(name string, f func(a, b Val) bool) {
			m[name] = func(in *OpInput) (Val, error) {
				a, b, err := ints2(in, w)
				if err != nil {
					return Val{}, err
				}
				return BoolVal(f(a, b)), nil
			}
		}
		cmp("Eq"+ws, func(a, b Val) bool { return a.Bits == b.Bits })
		cmp("Neq"+ws, func(a, b Val) bool { return a.Bits != b.Bits })
		cmp("Less"+ws, func(a, b Val) bool { return a.Int() < b.Int() })
		cmp("Leq"+ws, func(a, b Val) bool { return a.Int() <= b.Int() })
		cmp("Less"+ws+"U", func(a, b Val) bool { return a.Bits < b.Bits })
		cmp("Leq"+ws+"U", func(a, b Val) bool { return a.Bits <= b.Bits })

		// Shifts: AxB shifts an A-bit value by an unsigned B-bit amount.
		for _, cw := range []int{8, 16, 32, 64} {
			cw := cw
			for _, kind := range []string{"Lsh", "Rsh", "RshU"} {
				kind := kind
				name := fmt.Sprintf("%s%dx%d", kind[:3], w, cw)
				if kind == "RshU" {
					name = fmt.Sprintf("Rsh%dUx%d", w, cw)
				}
				m[name] = func(in *OpInput) (Val, error) {
					x, err := intArg(in, 0, w)
					if err != nil {
						return Val{}, err
					}
					s, err := intArg(in, 1, cw)
					if err != nil {
						return Val{}, err
					}
					amt := s.Bits
					if in.V.AuxInt != 0 && amt >= uint64(w) {
						return Val{}, undef(in, "shift marked bounded, but amount %d >= %d", amt, w)
					}
					switch kind {
					case "Lsh":
						if amt >= uint64(w) {
							return IntVal(w, 0), nil
						}
						return IntVal(w, x.Bits<<amt), nil
					case "RshU":
						if amt >= uint64(w) {
							return IntVal(w, 0), nil
						}
						return IntVal(w, x.Bits>>amt), nil
					}
					amt = min(amt, uint64(w-1))
					return IntVal(w, uint64(x.Int()>>amt)), nil
				}
			}
		}
	}

	for _, from := range []int{8, 16, 32, 64} {
		for _, to := range []int{8, 16, 32, 64} {
			from, to := from, to
			if from > to {
				m[fmt.Sprintf("Trunc%dto%d", from, to)] = func(in *OpInput) (Val, error) {
					x, err := intArg(in, 0, from)
					return IntVal(to, x.Bits), err
				}
			}
			if from < to {
				m[fmt.Sprintf("ZeroExt%dto%d", from, to)] = func(in *OpInput) (Val, error) {
					x, err := intArg(in, 0, from)
					return IntVal(to, x.Bits), err
				}
				m[fmt.Sprintf("SignExt%dto%d", from, to)] = func(in *OpInput) (Val, error) {
					x, err := intArg(in, 0, from)
					return IntVal(to, uint64(x.Int())), err
				}
			}
		}
	}

	// Conversions between integers and floats.
	for _, iw := range []int{32, 64} {
		for _, fw := range []int{32, 64} {
			for _, u := range []string{"", "U"} {
				iw, fw, u := iw, fw, u
				m[fmt.Sprintf("Cvt%d%sto%dF", iw, u, fw)] = func(in *OpInput) (Val, error) {
					x, err := intArg(in, 0, iw)
					if err != nil {
						return Val{}, err
					}
					if u == "U" {
						if fw == 32 {
							return Float32Val(float32(x.Bits)), nil
						}
						return FloatVal(64, float64(x.Bits)), nil
					}
					if fw == 32 {
						return Float32Val(float32(x.Int())), nil
					}
					return FloatVal(64, float64(x.Int())), nil
				}
				m[fmt.Sprintf("Cvt%dFto%d%s", fw, iw, u)] = func(in *OpInput) (Val, error) {
					x, err := floatArg(in, 0, fw)
					if err != nil {
						return Val{}, err
					}
					t := math.Trunc(x.Float())
					lo, hi := -math.Ldexp(1, iw-1), math.Ldexp(1, iw-1)
					if u == "U" {
						lo, hi = 0, math.Ldexp(1, iw)
					}
					if math.IsNaN(t) || t < lo || t >= hi {
						return Val{}, &Unspecified{in.V.OpName(), fmt.Sprintf("%v is out of range", x)}
					}
					if u == "U" {
						return IntVal(iw, uint64(t)), nil
					}
					return IntVal(iw, uint64(int64(t))), nil
				}
			}
		}
	}
	m["Cvt32Fto64F"] = func(in *OpInput) (Val, error) {
		x, err := floatArg(in, 0, 32)
		return FloatVal(64, x.Float()), err
	}
	m["Cvt64Fto32F"] = func(in *OpInput) (Val, error) {
		x, err := floatArg(in, 0, 64)
		return FloatVal(32, x.Float()), err
	}

	for _, w := range []int{32, 64} {
		w := w
		ws := strconv.Itoa(w)
		rnd := func(f float64) Val { return FloatVal(w, f) }
		fbin := func(name string, f32 func(a, b float32) float32, f64 func(a, b float64) float64) {
			m[name] = func(in *OpInput) (Val, error) {
				a, err := floatArg(in, 0, w)
				if err != nil {
					return Val{}, err
				}
				b, err := floatArg(in, 1, w)
				if err != nil {
					return Val{}, err
				}
				if w == 32 {
					return Float32Val(f32(float32(a.Float()), float32(b.Float()))), nil
				}
				return FloatVal(64, f64(a.Float(), b.Float())), nil
			}
		}
		fbin("Add"+ws+"F", func(a, b float32) float32 { return a + b }, func(a, b float64) float64 { return a + b })
		fbin("Sub"+ws+"F", func(a, b float32) float32 { return a - b }, func(a, b float64) float64 { return a - b })
		fbin("Mul"+ws+"F", func(a, b float32) float32 { return a * b }, func(a, b float64) float64 { return a * b })
		fbin("Div"+ws+"F", func(a, b float32) float32 { return a / b }, func(a, b float64) float64 { return a / b })
		// Go's min and max: NaN if either is NaN, and -0 < +0.
		fbin("Min"+ws+"F", func(a, b float32) float32 { return min(a, b) }, func(a, b float64) float64 { return min(a, b) })
		fbin("Max"+ws+"F", func(a, b float32) float32 { return max(a, b) }, func(a, b float64) float64 { return max(a, b) })
		fbin("Min"+ws+"FSel", func(a, b float32) float32 {
			if a < b {
				return a
			}
			return b
		}, func(a, b float64) float64 {
			if a < b {
				return a
			}
			return b
		})
		fbin("Max"+ws+"FSel", func(a, b float32) float32 {
			if a > b {
				return a
			}
			return b
		}, func(a, b float64) float64 {
			if a > b {
				return a
			}
			return b
		})
		m["Neg"+ws+"F"] = func(in *OpInput) (Val, error) {
			a, err := floatArg(in, 0, w)
			a.Bits ^= 1 << uint(w-1)
			return a, err
		}
		fcmp := func(name string, f func(a, b float64) bool) {
			m[name] = func(in *OpInput) (Val, error) {
				a, err := floatArg(in, 0, w)
				if err != nil {
					return Val{}, err
				}
				b, err := floatArg(in, 1, w)
				return BoolVal(f(a.Float(), b.Float())), err
			}
		}
		fcmp("Eq"+ws+"F", func(a, b float64) bool { return a == b })
		fcmp("Neq"+ws+"F", func(a, b float64) bool { return a != b })
		fcmp("Less"+ws+"F", func(a, b float64) bool { return a < b })
		fcmp("Leq"+ws+"F", func(a, b float64) bool { return a <= b })
		m["Const"+ws+"F"] = func(in *OpInput) (Val, error) {
			return rnd(math.Float64frombits(uint64(in.V.AuxInt))), nil
		}
		// Round32F and Round64F only force rounding to their precision,
		// which this model always does.
		m["Round"+ws+"F"] = func(in *OpInput) (Val, error) { return floatArg(in, 0, w) }
	}
	f64un := func(name string, f func(float64) float64) {
		m[name] = func(in *OpInput) (Val, error) {
			x, err := floatArg(in, 0, 64)
			return FloatVal(64, f(x.Float())), err
		}
	}
	f64un("Sqrt", math.Sqrt)
	f64un("Floor", math.Floor)
	f64un("Ceil", math.Ceil)
	f64un("Trunc", math.Trunc)
	f64un("Round", math.Round)
	f64un("RoundToEven", math.RoundToEven)
	f64un("Abs", math.Abs)
	m["Sqrt32"] = func(in *OpInput) (Val, error) {
		x, err := floatArg(in, 0, 32)
		return Float32Val(float32(math.Sqrt(x.Float()))), err
	}
	m["Copysign"] = func(in *OpInput) (Val, error) {
		a, err := floatArg(in, 0, 64)
		if err != nil {
			return Val{}, err
		}
		b, err := floatArg(in, 1, 64)
		return FloatVal(64, math.Copysign(a.Float(), b.Float())), err
	}
	m["FMA"] = func(in *OpInput) (Val, error) {
		var x [3]float64
		for i := range x {
			a, err := floatArg(in, i, 64)
			if err != nil {
				return Val{}, err
			}
			x[i] = a.Float()
		}
		return FloatVal(64, math.FMA(x[0], x[1], x[2])), nil
	}

	m["ConstBool"] = func(in *OpInput) (Val, error) { return BoolVal(in.V.AuxInt != 0), nil }
	m["Not"] = func(in *OpInput) (Val, error) {
		a, err := boolArg(in, 0)
		return BoolVal(!a.Bool()), err
	}
	bbin := func(name string, f func(a, b bool) bool) {
		m[name] = func(in *OpInput) (Val, error) {
			a, err := boolArg(in, 0)
			if err != nil {
				return Val{}, err
			}
			b, err := boolArg(in, 1)
			return BoolVal(f(a.Bool(), b.Bool())), err
		}
	}
	bbin("AndB", func(a, b bool) bool { return a && b })
	bbin("OrB", func(a, b bool) bool { return a || b })
	bbin("EqB", func(a, b bool) bool { return a == b })
	bbin("NeqB", func(a, b bool) bool { return a != b })
	m["CvtBoolToUint8"] = func(in *OpInput) (Val, error) {
		a, err := boolArg(in, 0)
		return IntVal(8, a.Bits), err
	}

	m["Copy"] = func(in *OpInput) (Val, error) { return in.Args[0], nil }
	m["Last"] = func(in *OpInput) (Val, error) {
		if len(in.Args) == 0 {
			return Val{}, illTyped(in, "no args")
		}
		return in.Args[len(in.Args)-1], nil
	}
	m["CondSelect"] = func(in *OpInput) (Val, error) {
		c, err := boolArg(in, 2)
		if err != nil {
			return Val{}, err
		}
		i := 1
		if c.Bool() {
			i = 0
		}
		if t := in.V.Type; t != nil && t.IsInteger() {
			return intArg(in, i, t.Bits())
		}
		return in.Args[i], nil
	}

	// Bounds checks: both args have the same (integer) type; arg1 >= 0.
	bounds := func(name string, f func(i, n int64) bool) {
		m[name] = func(in *OpInput) (Val, error) {
			i, err := intArg(in, 0, 0)
			if err != nil {
				return Val{}, err
			}
			n, err := intArg(in, 1, i.Width)
			if err != nil {
				return Val{}, err
			}
			if n.Int() < 0 {
				return Val{}, undef(in, "arg1 is negative")
			}
			return BoolVal(f(i.Int(), n.Int())), nil
		}
	}
	bounds("IsInBounds", func(i, n int64) bool { return 0 <= i && i < n })
	bounds("IsSliceInBounds", func(i, n int64) bool { return 0 <= i && i <= n })

	m["Hmul32"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 32)
		return IntVal(32, uint64((a.Int()*b.Int())>>32)), err
	}
	m["Hmul32u"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 32)
		return IntVal(32, (a.Bits*b.Bits)>>32), err
	}
	m["Hmul64u"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 64)
		hi, _ := bits.Mul64(a.Bits, b.Bits)
		return IntVal(64, hi), err
	}
	m["Hmul64"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 64)
		hi, _ := bits.Mul64(a.Bits, b.Bits)
		if a.Int() < 0 {
			hi -= b.Bits
		}
		if b.Int() < 0 {
			hi -= a.Bits
		}
		return IntVal(64, hi), err
	}
	for _, w := range []int{32, 64} {
		w := w
		m[fmt.Sprintf("Avg%du", w)] = func(in *OpInput) (Val, error) {
			a, b, err := ints2(in, w)
			if err != nil {
				return Val{}, err
			}
			if a.Bits < b.Bits {
				return Val{}, undef(in, "arg0 < arg1")
			}
			return IntVal(w, (a.Bits&b.Bits)+(a.Bits^b.Bits)>>1), nil
		}
	}
	m["Mul32uhilo"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 32)
		p := a.Bits * b.Bits
		return TupleVal(IntVal(32, p>>32), IntVal(32, p)), err
	}
	m["Mul64uhilo"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 64)
		hi, lo := bits.Mul64(a.Bits, b.Bits)
		return TupleVal(IntVal(64, hi), IntVal(64, lo)), err
	}
	m["Mul32uover"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 32)
		p := a.Bits * b.Bits
		return TupleVal(IntVal(32, p), BoolVal(p>>32 != 0)), err
	}
	m["Mul64uover"] = func(in *OpInput) (Val, error) {
		a, b, err := ints2(in, 64)
		hi, lo := bits.Mul64(a.Bits, b.Bits)
		return TupleVal(IntVal(64, lo), BoolVal(hi != 0)), err
	}
	m["Div128u"] = func(in *OpInput) (Val, error) {
		hi, err := intArg(in, 0, 64)
		if err != nil {
			return Val{}, err
		}
		lo, y, err := func() (Val, Val, error) {
			lo, err := intArg(in, 1, 64)
			if err != nil {
				return Val{}, Val{}, err
			}
			y, err := intArg(in, 2, 64)
			return lo, y, err
		}()
		if err != nil {
			return Val{}, err
		}
		if y.Bits == 0 || hi.Bits >= y.Bits {
			return Val{}, undef(in, "quotient overflows")
		}
		q, r := bits.Div64(hi.Bits, lo.Bits, y.Bits)
		return TupleVal(IntVal(64, q), IntVal(64, r)), nil
	}
	carry64 := func(name string, f func(x, y, c uint64) (uint64, uint64)) {
		m[name] = func(in *OpInput) (Val, error) {
			x, y, err := ints2(in, 64)
			if err != nil {
				return Val{}, err
			}
			c, err := intArg(in, 2, 64)
			if err != nil {
				return Val{}, err
			}
			if c.Bits > 1 {
				return Val{}, undef(in, "carry arg is %d, not 0 or 1", c.Bits)
			}
			s, co := f(x.Bits, y.Bits, c.Bits)
			return TupleVal(IntVal(64, s), IntVal(64, co)), nil
		}
	}
	carry64("Add64carry", bits.Add64)
	carry64("Sub64borrow", bits.Sub64)

	// 32-bit carry chains, as used by dec64. The flags hold the carry
	// (or borrow) bit.
	flagsVal := func(c uint32) Val { return Val{Kind: KFlags, Bits: uint64(c)} }
	m["Add32carry"] = func(in *OpInput) (Val, error) {
		x, y, err := ints2(in, 32)
		s, c := bits.Add32(uint32(x.Bits), uint32(y.Bits), 0)
		return TupleVal(IntVal(32, uint64(s)), flagsVal(c)), err
	}
	m["Add32carrywithcarry"] = func(in *OpInput) (Val, error) {
		x, y, err := ints2(in, 32)
		if err != nil {
			return Val{}, err
		}
		f, err := flagsArg(in, 2)
		s, c := bits.Add32(uint32(x.Bits), uint32(y.Bits), uint32(f.Bits))
		return TupleVal(IntVal(32, uint64(s)), flagsVal(c)), err
	}
	m["Add32withcarry"] = func(in *OpInput) (Val, error) {
		x, y, err := ints2(in, 32)
		if err != nil {
			return Val{}, err
		}
		f, err := flagsArg(in, 2)
		return IntVal(32, x.Bits+y.Bits+f.Bits), err
	}
	m["Sub32carry"] = func(in *OpInput) (Val, error) {
		x, y, err := ints2(in, 32)
		d, b := bits.Sub32(uint32(x.Bits), uint32(y.Bits), 0)
		return TupleVal(IntVal(32, uint64(d)), flagsVal(b)), err
	}
	m["Sub32withcarry"] = func(in *OpInput) (Val, error) {
		x, y, err := ints2(in, 32)
		if err != nil {
			return Val{}, err
		}
		f, err := flagsArg(in, 2)
		return IntVal(32, x.Bits-y.Bits-f.Bits), err
	}

	m["Int64Make"] = func(in *OpInput) (Val, error) {
		hi, lo, err := ints2(in, 32)
		return IntVal(64, hi.Bits<<32|lo.Bits), err
	}
	m["Int64Hi"] = func(in *OpInput) (Val, error) {
		x, err := intArg(in, 0, 64)
		return IntVal(32, x.Bits>>32), err
	}
	m["Int64Lo"] = func(in *OpInput) (Val, error) {
		x, err := intArg(in, 0, 64)
		return IntVal(32, x.Bits), err
	}
	m["Signmask"] = func(in *OpInput) (Val, error) {
		x, err := intArg(in, 0, 32)
		return IntVal(32, uint64(x.Int()>>31)), err
	}
	m["Zeromask"] = func(in *OpInput) (Val, error) {
		x, err := intArg(in, 0, 32)
		if x.Bits != 0 {
			return IntVal(32, math.MaxUint32), err
		}
		return IntVal(32, 0), err
	}
	m["Slicemask"] = func(in *OpInput) (Val, error) {
		x, err := intArg(in, 0, 0)
		if err != nil {
			return Val{}, err
		}
		w, err := typeWidth(in)
		if err != nil {
			return Val{}, err
		}
		if x.Width != w {
			return Val{}, illTyped(in, "arg0 is %s, want %d-bit integer", describe(x), w)
		}
		switch {
		case x.Int() < 0:
			return Val{}, undef(in, "arg0 is negative")
		case x.Int() == 0:
			return IntVal(w, 0), nil
		}
		return IntVal(w, math.MaxUint64), nil
	}

	m["Ctz64On32"] = func(in *OpInput) (Val, error) {
		lo, hi, err := ints2(in, 32)
		if err != nil {
			return Val{}, err
		}
		w, err := typeWidth(in)
		return IntVal(w, uint64(bits.TrailingZeros64(hi.Bits<<32|lo.Bits))), err
	}
	// Pointers.
	m["ConstNil"] = func(in *OpInput) (Val, error) { return PtrVal(int(in.Cfg.PtrSize*8), 0, 0), nil }
	addr := func(in *OpInput) (Val, error) {
		sym, ok := in.V.Aux.(*Sym)
		if !ok {
			return Val{}, illTyped(in, "aux is not a symbol")
		}
		return PtrVal(int(in.Cfg.PtrSize*8), sym.Obj, 0), nil
	}
	m["Addr"] = addr
	m["LocalAddr"] = addr
	// advance returns p advanced by off bytes. A pointer into an object
	// stays within the address space: no object spans it.
	advance := func(in *OpInput, p Val, off int64) (Val, error) {
		sum := p.Int() + off
		if p.Base != 0 && (sum != sext(uint64(sum), p.Width) || (off > 0) != (sum > p.Int()) && off != 0) {
			return Val{}, undef(in, "offset overflows the address space")
		}
		return PtrVal(p.Width, p.Base, uint64(sum)), nil
	}
	m["OffPtr"] = func(in *OpInput) (Val, error) {
		p, err := ptrArg(in, 0)
		if err != nil {
			return Val{}, err
		}
		return advance(in, p, in.V.AuxInt)
	}
	m["AddPtr"] = func(in *OpInput) (Val, error) {
		p, err := ptrArg(in, 0)
		if err != nil {
			return Val{}, err
		}
		i, err := intArg(in, 1, p.Width)
		if err != nil {
			return Val{}, err
		}
		return advance(in, p, i.Int())
	}
	ptrCmp := func(eq bool) OpFunc {
		return func(in *OpInput) (Val, error) {
			a, err := ptrArg(in, 0)
			if err != nil {
				return Val{}, err
			}
			b, err := ptrArg(in, 1)
			return BoolVal(a.Equal(b) == eq), err
		}
	}
	m["EqPtr"] = ptrCmp(true)
	m["NeqPtr"] = ptrCmp(false)
	m["IsNonNil"] = func(in *OpInput) (Val, error) {
		p, err := ptrArg(in, 0)
		return BoolVal(p.Base != 0 || p.Bits != 0), err
	}
	// Convert converts between unsafe.Pointer and uintptr; arg1 is memory.
	m["Convert"] = func(in *OpInput) (Val, error) { return in.Args[0], nil }

	m["MakeTuple"] = func(in *OpInput) (Val, error) { return TupleVal(in.Args[0], in.Args[1]), nil }
	for i, name := range []string{"Select0", "Select1"} {
		i := i
		m[name] = func(in *OpInput) (Val, error) {
			t := in.Args[0]
			if t.Kind != KTuple {
				return Val{}, illTyped(in, "arg0 is %s, want a tuple", describe(t))
			}
			return t.Elems[i], nil
		}
	}
	return m
}

// divmod implements Div and Mod.
func divmod(in *OpInput, w int, unsigned, isMod bool) (Val, error) {
	a, b, err := ints2(in, w)
	if err != nil {
		return Val{}, err
	}
	if b.Bits == 0 {
		// The value is valid SSA; the machine traps or computes
		// something machine-dependent.
		return Val{}, &Unspecified{in.V.OpName(), "division by zero"}
	}
	if unsigned {
		// prove turns a signed division with non-negative args into an
		// unsigned one without changing its type (see unsignedOp in
		// prove.go), and divmod.rules relies on that: an unsigned
		// division of a signed type has non-negative args.
		if t := in.V.Type; t != nil && t.IsSigned() && (a.Int() < 0 || b.Int() < 0) {
			return Val{}, undef(in, "unsigned division of signed type %v with a negative arg", t)
		}
		if isMod {
			return IntVal(w, a.Bits%b.Bits), nil
		}
		return IntVal(w, a.Bits/b.Bits), nil
	}
	x, y := a.Int(), b.Int()
	// For Div16/32/64, a non-zero AuxInt promises that the divisor is
	// not -1 or the dividend is not the most negative value; for
	// Mod16/32/64, that the divisor is not -1 (genericOps.go).
	if isMod && y == -1 && in.V.AuxInt != 0 && w > 8 {
		return Val{}, undef(in, "AuxInt promises the divisor is not -1")
	}
	if y == -1 && x == sext(1<<uint(w-1), w) {
		if in.V.AuxInt != 0 && w > 8 {
			return Val{}, undef(in, "AuxInt promises no most-negative / -1")
		}
		if isMod {
			return IntVal(w, 0), nil
		}
		return IntVal(w, uint64(x)), nil
	}
	if isMod {
		return IntVal(w, uint64(x%y)), nil
	}
	return IntVal(w, uint64(x/y)), nil
}
