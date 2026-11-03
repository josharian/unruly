package gensem

import (
	"math"
	"math/big"
	"math/bits"
	"math/rand/v2"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/ops"
)

// eval applies the generic op named name to args.
func eval(t *testing.T, tables *ops.Tables, name string, typ *Type, auxInt int64, args ...Val) (Val, error) {
	t.Helper()
	op := tables.Generic.Op(name)
	if op == nil {
		t.Fatalf("no op %s", name)
	}
	v := &Value{Op: op, Type: typ, AuxInt: auxInt}
	for _, a := range args {
		v.Args = append(v.Args, &Value{Leaf: a})
	}
	return NewInterp(Configs[0], GenericOps()).Eval(v)
}

// TestAgainstGo checks integer op semantics against Go's operators.
func TestAgainstGo(t *testing.T) {
	tables := analysistest.Tables(t)
	u := NewUniverse(8)
	r := rand.New(rand.NewPCG(1, 2))
	type binop struct {
		name string
		f    func(a, b int64, w int) (int64, bool) // result, defined
	}
	shiftCount := func(b int64) uint64 { return uint64(b) }
	binops := []binop{
		{"Add", func(a, b int64, w int) (int64, bool) { return a + b, true }},
		{"Mul", func(a, b int64, w int) (int64, bool) { return a * b, true }},
		{"Div", func(a, b int64, w int) (int64, bool) {
			if b == 0 {
				return 0, false
			}
			if b == -1 {
				return -a, true // wraps, as in Go
			}
			return a / b, true
		}},
		{"Mod", func(a, b int64, w int) (int64, bool) {
			if b == 0 {
				return 0, false
			}
			if b == -1 {
				return 0, true
			}
			return a % b, true
		}},
	}
	for _, w := range []int{8, 16, 32, 64} {
		typ := u.Int(int64(w/8), true)
		for range 2000 {
			a, b := sext(r.Uint64(), w), sext(r.Uint64()>>uint(r.IntN(64)), w)
			for _, op := range binops {
				want, ok := op.f(a, b, w)
				got, err := eval(t, tables, op.name+itoa(w), typ, 0, IntVal(w, uint64(a)), IntVal(w, uint64(b)))
				if !ok {
					if err == nil {
						t.Errorf("%s%d(%d, %d) = %v, want an error", op.name, w, a, b, got)
					}
					continue
				}
				if err != nil || got.Int() != sext(uint64(want), w) {
					t.Errorf("%s%d(%d, %d) = %v, %v; want %d", op.name, w, a, b, got, err, sext(uint64(want), w))
				}
			}
			// Shifts by a 64-bit count, with Go's semantics.
			n := shiftCount(b)
			if r.IntN(2) == 0 {
				n %= uint64(w + 4)
			}
			cnt := IntVal(64, n)
			ua := uint64(a) & mask(w)
			check := func(name string, want uint64) {
				got, err := eval(t, tables, name, typ, 0, IntVal(w, uint64(a)), cnt)
				if err != nil || got.Bits != want&mask(w) {
					t.Errorf("%s(%d, %d) = %v, %v; want %d", name, a, n, got, err, want&mask(w))
				}
			}
			var lsh, rsh, rshu uint64
			if n < 64 {
				lsh, rshu = ua<<n, ua>>n
				rsh = uint64(a >> n)
			} else {
				rsh = uint64(a >> 63)
			}
			check("Lsh"+itoa(w)+"x64", lsh)
			check("Rsh"+itoa(w)+"Ux64", rshu)
			check("Rsh"+itoa(w)+"x64", rsh)
		}
	}
}

// TestHmul checks the high-multiply ops against big.Int.
func TestHmul(t *testing.T) {
	tables := analysistest.Tables(t)
	u := NewUniverse(8)
	r := rand.New(rand.NewPCG(3, 4))
	for range 5000 {
		a, b := int64(r.Uint64()), int64(r.Uint64()>>uint(r.IntN(64)))
		p := new(big.Int).Mul(big.NewInt(a), big.NewInt(b))
		want := new(big.Int).Rsh(p, 64).Int64()
		got, err := eval(t, tables, "Hmul64", u.Named("Int64"), 0, IntVal(64, uint64(a)), IntVal(64, uint64(b)))
		if err != nil || got.Int() != want {
			t.Errorf("Hmul64(%d, %d) = %v, %v; want %d", a, b, got, err, want)
		}
		hi, _ := bits.Mul64(uint64(a), uint64(b))
		got, err = eval(t, tables, "Hmul64u", u.Named("UInt64"), 0, IntVal(64, uint64(a)), IntVal(64, uint64(b)))
		if err != nil || got.Bits != hi {
			t.Errorf("Hmul64u(%d, %d) = %v, %v; want %d", a, b, got, err, hi)
		}
		a32, b32 := int64(int32(a)), int64(int32(b))
		got, err = eval(t, tables, "Hmul32", u.Named("Int32"), 0, IntVal(32, uint64(a32)), IntVal(32, uint64(b32)))
		if err != nil || got.Int() != (a32*b32)>>32 {
			t.Errorf("Hmul32(%d, %d) = %v, %v; want %d", a32, b32, got, err, (a32*b32)>>32)
		}
	}
}

// TestMagic checks the copied magic-number helpers by dividing with them.
func TestMagic(t *testing.T) {
	r := rand.New(rand.NewPCG(5, 6))
	for range 2000 {
		c := int64(r.Uint32()>>uint(r.IntN(32))) | 3
		if c&(c-1) == 0 || c >= 1<<32 {
			continue
		}
		m := umagic(32, c)
		x := uint64(r.Uint32())
		// x / c == (x * (1<<32 + m)) >> (32 + s), per magic.go.
		hi, lo := bits.Mul64(x, 1<<32+m["M"])
		s := 32 + uint(m["S"])
		got := lo>>s | hi<<(64-s)
		if got != x/uint64(c) {
			t.Errorf("umagic(32, %d): %d/%d = %d, want %d", c, x, c, got, x/uint64(c))
		}
	}
}

// TestFloatConversion checks that out-of-range conversions are reported as
// machine-dependent rather than given a value.
func TestFloatConversion(t *testing.T) {
	tables := analysistest.Tables(t)
	u := NewUniverse(8)
	for _, f := range []float64{1 << 63, -1 << 64, math.NaN(), math.Inf(1)} {
		_, err := eval(t, tables, "Cvt64Fto64", u.Named("Int64"), 0, FloatVal(64, f))
		if _, ok := err.(*Unspecified); !ok {
			t.Errorf("Cvt64Fto64(%v): err = %v, want *Unspecified", f, err)
		}
	}
	got, err := eval(t, tables, "Cvt64Fto64", u.Named("Int64"), 0, FloatVal(64, -1<<63))
	if err != nil || got.Int() != math.MinInt64 {
		t.Errorf("Cvt64Fto64(-1<<63) = %v, %v", got, err)
	}
}
