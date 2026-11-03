package condsem

import (
	"fmt"
	"math"
	"math/bits"
	"strings"
)

// kind is the kind of an abstract value.
type kind uint8

const (
	kNone  kind = iota
	kInt        // i, with w meaningful low bits
	kFloat      // f; w is 32 or 64
	kFlags      // fl
	kSym        // an opaque value, named s (a match variable passed through unexamined)
	kSucc       // a block successor, named s
	kStore      // a byte store: xs = ptr, value, mem; s describes the address
	kTuple      // xs
)

// val is the value of an s-expression under one assignment of its variables.
type val struct {
	k  kind
	i  uint64
	w  uint8
	f  float64
	fl *flags
	s  string
	xs []val
}

func intVal(i uint64, w uint8) val { return val{k: kInt, i: trunc(i, w), w: w} }
func boolVal(b bool) val           { return intVal(b2u(b), 8) }
func symVal(s string) val          { return val{k: kSym, s: s} }
func floatVal(f float64, w uint8) val {
	if w == 32 {
		f = float64(float32(f))
	}
	return val{k: kFloat, f: f, w: w}
}

func b2u(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}

// trunc zero-extends the low w bits of x.
func trunc(x uint64, w uint8) uint64 {
	if w >= 64 {
		return x
	}
	return x & (1<<w - 1)
}

// sext sign-extends the low w bits of x.
func sext(x uint64, w uint8) int64 {
	if w >= 64 {
		return int64(x)
	}
	s := 64 - w
	return int64(x<<s) >> s
}

func (v val) String() string {
	switch v.k {
	case kInt:
		return fmtInt(v.i, v.w)
	case kFloat:
		return fmt.Sprint(v.f)
	case kFlags:
		return v.fl.String()
	case kSym, kSucc:
		return v.s
	case kStore:
		return fmt.Sprintf("store %s <- %v", v.s, v.xs[1])
	case kTuple:
		var s []string
		for _, x := range v.xs {
			s = append(s, x.String())
		}
		return "(" + strings.Join(s, ", ") + ")"
	}
	return "?"
}

// A flag bit, in the vocabulary of whichever arch is being modeled.
type bit uint8

const (
	bZ   bit = iota // zero (x86 ZF, ARM Z)
	bN              // negative (x86 SF, ARM N)
	bC              // carry (x86 CF: borrow on subtract; ARM C: no borrow on subtract)
	bV              // signed overflow (x86 OF, ARM V)
	bP              // x86 PF: parity of the low byte, or unordered after UCOMIS
	bNxV            // N != V, kept separately for flag constants that record only it
	bLT             // PPC64 CR bits
	bGT
	bEQ
	bSO // PPC64 summary overflow, or unordered after FCMPU
	nbits
)

var bitNames = [nbits]string{"Z", "N", "C", "V", "P", "N^V", "LT", "GT", "EQ", "SO"}

// origin says how a flags value was produced.
type origin uint8

const (
	oNone    origin = iota
	oSub            // integer a - b (compare)
	oAdd            // integer a + b (compare negative)
	oLogic          // integer result a (test, and-with-flags)
	oFloat          // float compare of fa and fb
	oConst          // a flag constant op
	oBitTest        // x86 BT: C is bit b of a
	oArith          // arithmetic with carry: bits set directly
)

// flags is a flags value. It records how it was produced, so that
// InvertFlags can swap the operands, and the resulting flag bits.
type flags struct {
	op     string // producing op, for messages
	o      origin
	a, b   uint64
	w      uint8
	fa, fb float64
	signed bool   // PPC64: a signed compare
	aux    uint64 // oConst: the constant's encoding (ARM FlagConstant)
	inner  *flags // the operand of InvertFlags, if op is InvertFlags

	known uint16 // bits whose value is known
	stale uint16 // bits that hold whatever an earlier instruction left
	set   uint16 // values of known bits
}

func (f *flags) setBit(b bit, v bool) {
	f.known |= 1 << b
	if v {
		f.set |= 1 << b
	} else {
		f.set &^= 1 << b
	}
}

func (f *flags) markStale(bs ...bit) {
	for _, b := range bs {
		f.stale |= 1 << b
		f.known &^= 1 << b
	}
}

// get returns the value of b.
func (f *flags) get(b bit) tri {
	if f.known&(1<<b) != 0 {
		return tbool(f.set&(1<<b) != 0)
	}
	if b == bNxV {
		return f.get(bN).xor(f.get(bV))
	}
	if f.stale&(1<<b) != 0 {
		return tStale
	}
	return tSkip
}

func (f *flags) String() string {
	if f.op == "InvertFlags" {
		return "(InvertFlags " + f.inner.String() + ")"
	}
	switch f.o {
	case oSub, oAdd, oLogic, oBitTest:
		args := fmtInt(f.a, f.w)
		if f.o != oLogic {
			args += " " + fmtInt(f.b, f.w)
		}
		return fmt.Sprintf("(%s %s)", f.op, args)
	case oFloat:
		return fmt.Sprintf("(%s %v %v)", f.op, f.fa, f.fb)
	case oConst:
		if f.op == "FlagConstant" {
			var s []string
			for _, b := range []bit{bN, bZ, bC, bV} {
				if f.set&(1<<b) != 0 {
					s = append(s, bitNames[b])
				}
			}
			return fmt.Sprintf("(FlagConstant [%s])", strings.Join(s, ""))
		}
		return "(" + f.op + ")"
	}
	return f.op
}

func fmtInt(x uint64, w uint8) string {
	s := sext(x, w)
	if s > -1<<16 && s < 1<<16 {
		return fmt.Sprint(s)
	}
	if s == math.MinInt64 || s == math.MinInt32 || s == math.MinInt16 || s == math.MinInt8 {
		return fmt.Sprint(s)
	}
	return fmt.Sprintf("%#x", trunc(x, w))
}

// subFlags fills in the ZNCV flags of a - b at width w. carryIsBorrow
// selects x86's carry convention (C set on borrow) over ARM's (C set on no
// borrow).
func subFlags(f *flags, carryIsBorrow bool) {
	a, b, w := trunc(f.a, f.w), trunc(f.b, f.w), f.w
	r := trunc(a-b, w)
	f.setBit(bZ, r == 0)
	f.setBit(bN, sext(r, w) < 0)
	borrow := a < b
	f.setBit(bC, borrow == carryIsBorrow)
	sa, sb, sr := sext(a, w) < 0, sext(b, w) < 0, sext(r, w) < 0
	f.setBit(bV, sa != sb && sr != sa)
	f.setBit(bP, bits.OnesCount8(uint8(r))%2 == 0)
}

// addFlags fills in the ZNCV flags of a + b at width w (ARM conventions).
func addFlags(f *flags) {
	a, b, w := trunc(f.a, f.w), trunc(f.b, f.w), f.w
	r := trunc(a+b, w)
	f.setBit(bZ, r == 0)
	f.setBit(bN, sext(r, w) < 0)
	f.setBit(bC, r < a) // carry out of w bits
	sa, sb, sr := sext(a, w) < 0, sext(b, w) < 0, sext(r, w) < 0
	f.setBit(bV, sa == sb && sr != sa)
	f.setBit(bP, onesEven(r))
}

// tri is a three-valued truth: a condition may also read a flag that is
// meaningless in this state.
type tri uint8

const (
	tFalse tri = iota
	tTrue
	tSkip  // the flag is not modeled in this state (such as N alone of a flag constant that records only N^V)
	tStale // the flag holds whatever an earlier instruction left there
)

func tbool(b bool) tri {
	if b {
		return tTrue
	}
	return tFalse
}

func (t tri) known() bool { return t == tTrue || t == tFalse }

func unknownOf(a, b tri) tri {
	if a == tStale || b == tStale {
		return tStale
	}
	return tSkip
}

func (t tri) not() tri {
	switch t {
	case tTrue:
		return tFalse
	case tFalse:
		return tTrue
	}
	return t
}

func (t tri) and(u tri) tri {
	if t == tFalse || u == tFalse {
		return tFalse
	}
	if t == tTrue && u == tTrue {
		return tTrue
	}
	return unknownOf(t, u)
}

func (t tri) or(u tri) tri {
	if t == tTrue || u == tTrue {
		return tTrue
	}
	if t == tFalse && u == tFalse {
		return tFalse
	}
	return unknownOf(t, u)
}

func (t tri) xor(u tri) tri {
	if t.known() && u.known() {
		return tbool(t != u)
	}
	return unknownOf(t, u)
}

func (t tri) String() string {
	return [...]string{"false", "true", "unmodeled", "stale"}[t]
}

// fcat is the category of flags a condition reads.
type fcat uint8

const (
	catInt   fcat = 1 << iota // integer comparisons
	catFloat                  // floating-point comparisons
	catBoth  = catInt | catFloat
)

// A cond is a condition on flags, such as "signed less than".
type cond struct {
	name string
	cat  fcat
	eval func(f *flags) tri
}

// Panics used to abandon evaluation.
type (
	// skipRule abandons checking a rule: it uses something not modeled.
	skipRule struct{ reason string }
	// skipState abandons one assignment of the variables: it is not a
	// state the rule can match (such as a division by zero in a condition).
	skipState struct{}
)

func unmodeled(format string, args ...any) {
	panic(skipRule{fmt.Sprintf(format, args...)})
}

func impossible() { panic(skipState{}) }

// Domains for leaf variables. They are ordered by importance: when a rule
// has many variables, only a prefix of each domain is used.
var intDomain = []uint64{
	0, 1, ^uint64(0), 1 << 63, 1<<63 - 1, 0x80000000, 0x7fffffff, 2,
	0xffffffff, 0x80, 0x7f, 0xff, 0x8000, 0x7fff, 0xffff,
	1 << 32, 0xffffffff00000000, 0xffffffff80000000, 0x100, 0x10000,
	3, 7, 8, 16, 31, 32, 63, 64, 127, 128, 0x7ffffffe, ^uint64(1),
	0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 0x123456789,
}

var floatDomain = []float64{
	1, math.NaN(), 2, 0, math.Copysign(0, -1), -1, math.Inf(1), math.Inf(-1), 0.5,
}

// Operand pairs for enumerating flags produced by integer compares.
var flagOperands = []uint64{0, 1, ^uint64(0), 1 << 63, 1<<63 - 1, 0x80000000, 0x7fffffff, 0x80, 0x7f, 0x8000, 0x7fff, 2}
