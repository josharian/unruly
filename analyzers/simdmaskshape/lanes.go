package simdmaskshape

import (
	"fmt"
	"go/types"
	"maps"
	"math"
	"math/big"
	"math/rand/v2"
	"regexp"
	"slices"
	"strconv"
	"strings"

	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// This file evaluates AMD64 SIMD expressions on concrete values, so
// that a rule's match and result can be compared lane by lane. It
// models, from the Intel SDM:
//
//   - selects: VMOVDQU<E>Masked x k (k ? x : 0), VPBLENDM<X>Masked a b k
//     and VPBLENDVB/VBLENDVPS/VBLENDVPD a b m (m ? b : a);
//   - compares, into vectors (VPCMPEQ<X>, VPCMPGT<X>, VCMPP<S|D>) or K
//     masks (VPCMP[U]<X> [pred], VPCMPEQ<X>512, VCMPP<S|D>k [pred], ...);
//   - mask conversions VPMOVVec<E>x<N>ToM and VPMOVMToVec<E>x<N>;
//   - bitwise AND (VPAND, VPANDD, VPANDQ, VANDPS, VANDPD) and Zero.
//
// Operand order is that of amd64/ssa.go, which emits operands in reverse
// (Intel order dst, arg0, arg1, arg2): VPBLENDVB and VBLENDVP<S|D> by
// simdV31, VPBLENDM by simdV2kv, VPCMP<X> [imm] and VCMPP<S|D> by
// simdV2kImm8 and simdV21Imm8, VPCMPEQ/GT by simdV21 and simdV2k. So
// (VPCMPGTD128 p q) is p > q and (VPCMPD128 [6] p q) is p NLE q.
//
// Any other op's value is unknown, and so is every lane computed from
// it, unless it doesn't matter: a select between equal values, or a
// bit that AND makes zero. The checks compare only known lanes, so that
// they report only differences that hold whatever the other ops compute.

// A vreg is a vector register's bytes, little-endian. An op of width w
// uses the low w/8 bytes; the rest are zero.
type vreg [64]byte

func (v *vreg) get(w, i int) uint64 {
	var x uint64
	for b := w/8 - 1; b >= 0; b-- {
		x = x<<8 | uint64(v[i*w/8+b])
	}
	return x
}

func (v *vreg) set(w, i int, x uint64) {
	for b := range w / 8 {
		v[i*w/8+b] = byte(x >> (8 * b))
	}
}

// ones returns w one bits.
func ones(w int) uint64 { return ^uint64(0) >> (64 - w) }

// top reports whether the top bit of w-bit x is set.
func top(x uint64, w int) bool { return x>>(w-1)&1 != 0 }

// A val is the value of an expression: a vector, or a K mask's bits.
// Bit i of vu is set if byte i of v is unknown; bit i of ku, if bit i
// of k is.
type val struct {
	v      vreg
	k      uint64
	vu, ku uint64
}

// laneBytes returns the bits of vu for w-bit lane i.
func laneBytes(w, i int) uint64 { return ones(w/8) << (i * w / 8) }

// known reports whether w-bit lane i of x's vector is known.
func (x val) known(w, i int) bool { return x.vu&laneBytes(w, i) == 0 }

// setUnknown marks lane i of x unknown: bit i of its mask register if
// isK, else its w-bit vector lane.
func (x *val) setUnknown(w, i int, isK bool) {
	if isK {
		x.ku |= 1 << i
	} else {
		x.vu |= laneBytes(w, i)
	}
}

// byteBits returns the bits of the bytes whose bits are set in the low
// 8 bits of m.
func byteBits(m uint64) uint64 {
	var x uint64
	for b := range 8 {
		if m>>b&1 != 0 {
			x |= 0xff << (8 * b)
		}
	}
	return x
}

// An opKind classifies the ops the evaluator models.
type opKind int

const (
	opaqueOp  opKind = iota
	zeroOp           // Zero<B>
	cmpOp            // a compare
	toKOp            // VPMOVVec<E>x<N>ToM: bit i is the top bit of E-bit lane i
	toVecOp          // VPMOVMToVec<E>x<N>: E-bit lane i is all ones if bit i is set
	maskMovOp        // VMOVDQU<E>Masked x k: k ? x : 0
	blendKOp         // VPBLENDM<X>Masked a b k: k ? b : a
	blendVOp         // VPBLENDVB, VBLENDVP<S|D> a b m: top bit of m ? b : a
	bitOp            // bitwise ops on vectors
)

// An opInfo is what the evaluator knows of an op.
type opInfo struct {
	kind opKind
	bits int // vector width
	// w is the lane width: of a compare's elements, a select's lanes,
	// or a conversion's lanes.
	w     int
	lanes int    // toKOp, toVecOp: the number of lanes converted
	cmp   cmpDom // cmpOp
	fn    func(a, b uint64) uint64
}

// A cmpDom is what a compare op compares.
type cmpDom struct {
	dom string // "signed", "unsigned", or "float"
	// pred is the predicate the op implies, or -1 if it is the auxint.
	pred int64
}

var (
	cmpRE    = regexp.MustCompile(`^(?:VPCMP(EQ|GT|U|)([BWDQ])|VCMPP([SD]))$`)
	blendvRE = regexp.MustCompile(`^V(?:PBLENDV(B)|BLENDVP([SD]))$`)
	andRE    = regexp.MustCompile(`^(?:VPAND[DQ]?|VANDP[SD])$`)
	zeroRE   = regexp.MustCompile(`^Zero(128|256|512)$`)
	bitsRE   = regexp.MustCompile(`(128|256|512)`)
	sdWidth  = map[string]int{"S": 32, "D": 64}
)

// bitOps are the bitwise vector ops modeled, by asm.
var bitOps = []struct {
	re *regexp.Regexp
	fn func(a, b uint64) uint64
}{
	{andRE, func(a, b uint64) uint64 { return a & b }},
}

// opBits returns the vector width of op: its typ's, or for an op of typ
// Mask, the width in its name.
func opBits(op *ops.Op) int {
	if b := vecBits(op.Typ); b != 0 {
		return b
	}
	if m := bitsRE.FindString(op.Name); m != "" {
		n, _ := strconv.Atoi(m)
		return n
	}
	return 0
}

// writesMask reports whether op's result is a mask register.
func writesMask(op *ops.Op) bool {
	k := maskRegs(op.Arch)
	return len(op.Reg.Outputs) == 1 && !k.Empty() && !op.Reg.Outputs[0].Empty() && op.Reg.Outputs[0].Minus(k).Empty()
}

// classify returns what the evaluator knows of op, applied to n args.
func classify(op *ops.Op, n int) opInfo {
	if op == nil || op.IsGeneric() || int(op.ArgLength) != n {
		return opInfo{}
	}
	if m := maskOpRE.FindStringSubmatch(op.Name); m != nil && n == 1 {
		if m[1] != "" && vec2mRE.MatchString(op.Asm) {
			w, _ := strconv.Atoi(m[1])
			l, _ := strconv.Atoi(m[2])
			return opInfo{kind: toKOp, bits: w * l, w: w, lanes: l}
		}
		if m[3] != "" && m2vecRE.MatchString(op.Asm) {
			w, _ := strconv.Atoi(m[3])
			l, _ := strconv.Atoi(m[4])
			return opInfo{kind: toVecOp, bits: w * l, w: w, lanes: l}
		}
	}
	bits := opBits(op)
	if bits == 0 {
		return opInfo{}
	}
	if zeroRE.MatchString(op.Name) && n == 0 {
		return opInfo{kind: zeroOp, bits: bits}
	}
	if m := cmpRE.FindStringSubmatch(op.Asm); m != nil && n == 2 && maskArg(op) < 0 {
		c := cmpDom{dom: "signed", pred: -1}
		w := bwdqWidth[m[2]]
		switch {
		case m[3] != "":
			c.dom, w = "float", sdWidth[m[3]]
		case m[1] == "EQ":
			c.pred = 0
		case m[1] == "GT":
			c.pred = 6
		case m[1] == "U":
			c.dom = "unsigned"
		}
		return opInfo{kind: cmpOp, bits: bits, w: w, cmp: c}
	}
	if b := blendvRE.FindStringSubmatch(op.Asm); b != nil && n == 3 {
		w := 8
		if b[2] != "" {
			w = sdWidth[b[2]]
		}
		return opInfo{kind: blendVOp, bits: bits, w: w}
	}
	switch kind, w := wrapper(op); kind {
	case zeroWrapper:
		return opInfo{kind: maskMovOp, bits: bits, w: w}
	case mergeWrapper:
		return opInfo{kind: blendKOp, bits: bits, w: w}
	}
	if n == 2 && maskArg(op) < 0 && strings.HasPrefix(op.Typ, "Vec") {
		for _, b := range bitOps {
			if b.re.MatchString(op.Asm) {
				return opInfo{kind: bitOp, bits: bits, fn: b.fn}
			}
		}
	}
	return opInfo{}
}

// intRels and floatRels are the relations that predicates compute.
// VPCMP's 8 predicates are EQ, LT, LE, FALSE, NE, NLT, NLE, TRUE.
// VCMPP's 32 predicates, mod 16, are (Intel SDM Table 3-8, CMPPD) EQ_OQ,
// LT_OS, LE_OS, UNORD_Q, NEQ_UQ, NLT_US, NLE_US, ORD_Q, EQ_UQ, NGE_US,
// NGT_US, FALSE_OQ, NEQ_OQ, GE_OS, GT_OS, TRUE_UQ: an ordered relation,
// and the result when either operand is NaN. Predicates 16-31 differ
// from 0-15 only in signaling.
var (
	intRels   = [8]string{"==", "<", "<=", "false", "!=", ">=", ">", "true"}
	floatRels = [16]struct {
		rel   string
		unord bool
	}{
		{"==", false}, {"<", false}, {"<=", false}, {"false", true},
		{"!=", true}, {">=", true}, {">", true}, {"true", false},
		{"==", true}, {"<", true}, {"<=", true}, {"false", false},
		{"!=", false}, {">=", false}, {">", false}, {"true", true},
	}
	// floatPredNames are the names of VCMPP predicates, from the
	// Intel SDM's Table 3-8. Predicates 16..31 are 0..15 with the
	// other signaling behavior.
	floatPredNames = [32]string{"EQ_OQ", "LT_OS", "LE_OS", "UNORD_Q", "NEQ_UQ", "NLT_US", "NLE_US", "ORD_Q",
		"EQ_UQ", "NGE_US", "NGT_US", "FALSE_OQ", "NEQ_OQ", "GE_OS", "GT_OS", "TRUE_UQ",
		"EQ_OS", "LT_OQ", "LE_OQ", "UNORD_S", "NEQ_US", "NLT_UQ", "NLE_UQ", "ORD_S",
		"EQ_US", "NGE_UQ", "NGT_UQ", "FALSE_OS", "NEQ_OS", "GE_OQ", "GT_OQ", "TRUE_US"}
)

func relHolds(rel string, c int) bool {
	switch rel {
	case "==":
		return c == 0
	case "<":
		return c < 0
	case "<=":
		return c <= 0
	case "!=":
		return c != 0
	case ">=":
		return c >= 0
	case ">":
		return c > 0
	case "true":
		return true
	}
	return false
}

// float returns w-bit x as a float64.
func float(x uint64, w int) float64 {
	if w == 32 {
		return float64(math.Float32frombits(uint32(x)))
	}
	return math.Float64frombits(x)
}

func sext(x uint64, w int) int64 { return int64(x<<(64-w)) >> (64 - w) }

// compare reports whether w-bit elements a and b satisfy predicate pred.
func (c cmpDom) compare(pred int64, w int, a, b uint64) bool {
	if c.dom == "float" {
		x, y := float(a, w), float(b, w)
		r := floatRels[pred&15]
		if x != x || y != y {
			return r.unord
		}
		cmp := 0
		if x < y {
			cmp = -1
		} else if x > y {
			cmp = 1
		}
		return relHolds(r.rel, cmp)
	}
	cmp := 0
	if c.dom == "unsigned" {
		if a < b {
			cmp = -1
		} else if a > b {
			cmp = 1
		}
	} else {
		if x, y := sext(a, w), sext(b, w); x < y {
			cmp = -1
		} else if x > y {
			cmp = 1
		}
	}
	return relHolds(intRels[pred&7], cmp)
}

// describe says what comparing p and q with pred computes, e.g.
// "p > q on signed 32-bit integers".
// If the predicate is an expression, text is its text.
func (c cmpDom) describe(pred int64, text string, w int, p, q string) string {
	if c.dom == "float" {
		ps := fmt.Sprint(pred & 31)
		if text != "" {
			ps = fmt.Sprintf("%s = %d", text, pred&31)
		}
		return fmt.Sprintf("VCMPP predicate %s (%s) of %s, %s on float%d elements", ps, floatPredNames[pred&31], p, q, w)
	}
	rel := intRels[pred&7]
	what := p + " " + rel + " " + q
	if rel == "true" || rel == "false" {
		what = rel
	}
	dom := c.dom + " "
	if pred&3 == 0 {
		dom = "" // == and != ignore signedness
	}
	if text != "" {
		what = fmt.Sprintf("%s (%s = %d)", what, text, pred&7)
	}
	return fmt.Sprintf("%s on %s%d-bit integers", what, dom, w)
}

// An interp evaluates a rule's values on one assignment of its variables.
type interp struct {
	r  *rules.Rule
	tr *typecheck.Rule // nil if the rule doesn't type-check
	f  *facts.Facts
	// vals are the values of the rule's integer variables.
	vals map[types.Object]any
	// bound are the match's named compound values, which a result may
	// refer to by name.
	bound map[string]*rules.Value
	// wild names the match's _ leaves, which are distinct variables.
	wild map[*rules.Value]string

	// The variables' values in the current trial.
	rng    *rand.Rand
	shared []uint64
	vecs   map[string]*vreg
	ks     map[string]uint64
	// fill, if not -1, is every byte of every variable, so that
	// the first trials are all zeros and all ones.
	fill int
}

// newTrial picks new values for the variables, for trial t.
func (in *interp) newTrial(rng *rand.Rand, t int) {
	in.rng = rng
	in.fill = -1
	if t < 2 {
		in.fill = -t & 0xff
	}
	in.shared = []uint64{rng.Uint64(), rng.Uint64(), rng.Uint64()}
	in.vecs = map[string]*vreg{}
	in.ks = map[string]uint64{}
}

// elem returns a w-bit element value, likely an interesting one.
func (in *interp) elem(w int) uint64 {
	f32 := w == 32 || w == 64
	switch in.rng.IntN(12) {
	case 0:
		return 0
	case 1:
		return 1
	case 2:
		return ones(w)
	case 3:
		return 1 << (w - 1)
	case 4:
		return ones(w) >> 1
	case 5:
		if f32 {
			return map[int]uint64{32: 0x7fc00000, 64: 0x7ff8000000000000}[w] // NaN
		}
	case 6:
		if f32 {
			return map[int]uint64{32: 0x3f800000, 64: 0x3ff0000000000000}[w] // 1.0
		}
	case 7:
		if f32 {
			return map[int]uint64{32: 0xbf800000, 64: 0xbff0000000000000}[w] // -1.0
		}
	case 8, 9:
		return in.shared[in.rng.IntN(len(in.shared))] & ones(w)
	}
	return in.rng.Uint64() & ones(w)
}

// vecVar returns the value of vector variable name.
func (in *interp) vecVar(name string) *vreg {
	if v, ok := in.vecs[name]; ok {
		return v
	}
	v := new(vreg)
	if in.fill >= 0 {
		for i := range v {
			v[i] = byte(in.fill)
		}
		in.vecs[name] = v
		return v
	}
	w := 8 << in.rng.IntN(4)
	var like *vreg
	if len(in.vecs) > 0 && in.rng.IntN(3) == 0 {
		// Make lanes equal to another variable's, to exercise
		// comparisons of equal values.
		names := slices.Sorted(maps.Keys(in.vecs))
		like = in.vecs[names[in.rng.IntN(len(names))]]
	}
	for i := range 512 / w {
		if like != nil && in.rng.IntN(4) != 0 {
			v.set(w, i, like.get(w, i))
		} else {
			v.set(w, i, in.elem(w))
		}
	}
	in.vecs[name] = v
	return v
}

// kVar returns the value of mask register variable name.
func (in *interp) kVar(name string) uint64 {
	if k, ok := in.ks[name]; ok {
		return k
	}
	var k uint64
	switch {
	case in.fill >= 0:
		k = -uint64(in.fill & 1)
	default:
		k = in.rng.Uint64()
		switch in.rng.IntN(8) {
		case 0:
			k = 0
		case 1:
			k = ^uint64(0)
		}
	}
	in.ks[name] = k
	return k
}

// aux returns the value of v's auxint.
func (in *interp) aux(v *rules.Value) (int64, bool) {
	if v.AuxInt == "" || v.AuxInt == "_" {
		return 0, false
	}
	if in.tr != nil {
		if e := in.tr.Expr(v, typecheck.AuxInt); e != nil {
			x, ok := in.f.Eval(e, in.vals)
			b, ok2 := x.(*big.Int)
			if !ok || !ok2 || !b.IsInt64() {
				return 0, false
			}
			return b.Int64(), true
		}
	}
	n, err := strconv.ParseInt(v.AuxInt, 0, 64)
	return n, err == nil
}

// eval returns the value of v, a mask register if isK.
func (in *interp) eval(v *rules.Value, isK bool) val {
	if v.IsLeaf() {
		if b, ok := in.bound[v.Name]; ok {
			return in.eval(b, isK)
		}
		name := v.Name
		switch {
		case name == "_":
			name = in.wild[v] // each _ is a different value
		case !v.IsVar():
			return unknown() // a Go expression, such as v.Args[0]
		}
		if isK {
			return val{k: in.kVar(name)}
		}
		return val{v: *in.vecVar(name)}
	}
	info := classify(v.Op, len(v.Args))
	arg := func(i int) val {
		return in.eval(v.Args[i], info.kind == maskMovOp && i == 1 || info.kind == blendKOp && i == 2 || info.kind == toVecOp)
	}
	var out val
	w := info.w
	switch info.kind {
	case zeroOp:
	case cmpOp:
		pred := info.cmp.pred
		if pred < 0 {
			p, ok := in.aux(v)
			if !ok {
				return unknown()
			}
			pred = p
		}
		p, q := arg(0), arg(1)
		for i := range info.bits / w {
			switch {
			case !p.known(w, i) || !q.known(w, i):
				out.setUnknown(w, i, writesMask(v.Op))
			case !info.cmp.compare(pred, w, p.v.get(w, i), q.v.get(w, i)):
			case writesMask(v.Op):
				out.k |= 1 << i
			default:
				out.v.set(w, i, ones(w))
			}
		}
	case toKOp:
		m := arg(0)
		for i := range info.lanes {
			switch {
			case m.vu>>((i+1)*w/8-1)&1 != 0:
				out.ku |= 1 << i
			case top(m.v.get(w, i), w):
				out.k |= 1 << i
			}
		}
	case toVecOp:
		k := arg(0)
		for i := range info.lanes {
			switch {
			case k.ku>>i&1 != 0:
				out.vu |= laneBytes(w, i)
			case k.k>>i&1 != 0:
				out.v.set(w, i, ones(w))
			}
		}
	case maskMovOp:
		x, k := arg(0), arg(1)
		for i := range info.bits / w {
			out.sel(w, i, k.ku>>i&1 == 0, k.k>>i&1 != 0, x, val{})
		}
	case blendKOp:
		a, b, k := arg(0), arg(1), arg(2)
		for i := range info.bits / w {
			out.sel(w, i, k.ku>>i&1 == 0, k.k>>i&1 != 0, b, a)
		}
	case blendVOp:
		a, b, m := arg(0), arg(1), arg(2)
		for i := range info.bits / w {
			out.sel(w, i, m.vu>>((i+1)*w/8-1)&1 == 0, top(m.v.get(w, i), w), b, a)
		}
	case bitOp:
		a, b := arg(0), arg(1)
		for i := range info.bits / 64 {
			x, ux := a.v.get(64, i), byteBits(a.vu>>(8*i))
			y, uy := b.v.get(64, i), byteBits(b.vu>>(8*i))
			z, diff := bitwise(info.fn, x, ux, y, uy)
			out.v.set(64, i, z)
			for b := range 8 {
				if diff>>(8*b)&0xff != 0 {
					out.vu |= 1 << (8*i + b)
				}
			}
		}
	default:
		return unknown()
	}
	return out
}

// sel sets lane i of out to t if the mask is set, else to f. If the
// mask is unknown, the lane is known only if t and f agree.
func (out *val) sel(w, i int, known, set bool, t, f val) {
	src := f
	switch {
	case !known && (!t.known(w, i) || !f.known(w, i) || t.v.get(w, i) != f.v.get(w, i)):
		out.vu |= laneBytes(w, i)
		return
	case set:
		src = t
	}
	out.v.set(w, i, src.v.get(w, i))
	out.vu |= src.vu & laneBytes(w, i)
}

// unknown returns a value of which nothing is known: an unmodeled op's.
func unknown() val { return val{vu: ^uint64(0), ku: ^uint64(0)} }

// bitwise evaluates a per-bit function with unknown operand bits. A result
// bit is known if all possible inputs at that bit give the same result.
func bitwise(fn func(a, b uint64) uint64, a, au, b, bu uint64) (z, unknown uint64) {
	z = fn(a&^au, b&^bu)
	for _, x := range []uint64{a &^ au, a | au} {
		for _, y := range []uint64{b &^ bu, b | bu} {
			unknown |= fn(x, y) ^ z
		}
	}
	return
}
