// Package simdnames checks SIMD lowerings against what the names of the
// generic ops and the x86 mnemonics promise.
package simdnames

import (
	"fmt"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "simdnames",
	Doc: `check SIMD lowerings against the semantics their names promise

SIMD generic ops are named for their archsimd method and receiver type
(AddSaturatedUint8x16 is Uint8x16.AddSaturated), and x86 mnemonics encode
signedness and element widths (VPADDSB adds signed bytes with signed
saturation; VPADDUSB, unsigned). Lowerings are generated from tables in
which a slip lowers an op to a sibling instruction:

	(AddSaturatedUint8x16 ...) => (VPADDSB128 ...)

saturates unsigned lanes at signed bounds, so 200+100 is 127, not 255.
The checks:

  - Signedness and width: the receiver type of a lowered generic op must
    match the operand signedness and width of the x86 instruction it is
    lowered to (VPADDS/VPADDUS, VPMINS/VPMINU, VPMOVSX/VPMOVZX, VPSRA/VPSRL,
    VPMOVS/VPMOVUS, VPACKSS/VPACKUS, VPMADDUBSW, VCVT*, ...), and a
    "To<Type><N>" in the op's name must match the instruction's result.
  - Lane parity: MulAddEvenSubOdd (add in even lanes, subtract in odd
    ones) must lower to VFMSUBADD; MulAddOddSubEven to VFMADDSUB.
  - Collisions: a machine op (with a given aux) that is the lowering of two
    generic ops with different names (ignoring element types) is probably a
    copy-paste slip, as when SHA256Message2 lowered to SHA256MSG1.
  - K-register widths: a K-register op (KANDW, KMOVB, ...) feeding or fed by
    a conversion between K registers and N-lane vector masks
    (VPMOVMToVec<E>x<N>, VPMOVVec<E>x<N>ToM) must have at least N bits;
    KANDB on a 16-lane mask drops lanes 8-15.
  - And-not operand order: a rule rewriting one and-not op into another
    must complement the same operand. (VPANDN x y) is ^x & y (amd64
    simdV21 emits VPANDN y, x, dst) but (KANDNW x y) is x & ^y (emitted as
    KANDNW x, y, dst), so (VPANDN128 (VPMOVMToVec8x16 x) (VPMOVMToVec8x16 y))
    must become (KANDNW y x).

The mnemonic semantics are those of the Intel SDM. Mnemonics not in the
table are not checked.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		checkCollisions(pass, set)
		if set.Arch.Name != "AMD64" {
			continue
		}
		for _, r := range set.Rules {
			if r.IsBlock() || r.Match.Op == nil || r.Result == nil {
				continue
			}
			if r.Match.Op.IsGeneric() {
				checkMnemonics(pass, r)
				checkParity(pass, r)
			}
			checkKWidth(pass, r)
			checkAndNot(pass, r)
		}
	}
	return nil
}

// A typ is an element type parsed from a name: Kind is 's' (signed
// integer), 'u' (unsigned integer), or 'f' (float); Bits is its width.
// Zero fields mean "any".
type typ struct {
	Kind byte
	Bits int
}

func (t typ) String() string {
	k := map[byte]string{'s': "signed ", 'u': "unsigned ", 'f': "float"}[t.Kind]
	switch {
	case t.Bits == 0:
		return strings.TrimSpace(k)
	case t.Kind == 'f':
		return fmt.Sprintf("float%d", t.Bits)
	}
	return fmt.Sprintf("%s%d-bit", k, t.Bits)
}

// conflicts reports whether t and u cannot be the same type.
func (t typ) conflicts(u typ) bool {
	return t.Kind != 0 && u.Kind != 0 && t.Kind != u.Kind ||
		t.Bits != 0 && u.Bits != 0 && t.Bits != u.Bits
}

var kindOf = map[string]byte{"Int": 's', "Uint": 'u', "Float": 'f'}

// genericName splits a SIMD generic op name such as AddSaturatedUint8x16
// into its method name and receiver element type.
var genericNameRE = regexp.MustCompile(`^(\w+?)(Int|Uint|Float)(\d+)x(\d+)$`)

// toTypeRE finds the result type in a method name such as SaturateToUint8,
// ConvertToFloat32, or ConcatSaturateToInt16Grouped.
var toTypeRE = regexp.MustCompile(`To(Int|Uint|Float)(\d+)`)

func parseGeneric(name string) (method string, recv typ, ok bool) {
	m := genericNameRE.FindStringSubmatch(name)
	if m == nil {
		return "", typ{}, false
	}
	b, _ := strconv.Atoi(m[3])
	return m[1], typ{kindOf[m[2]], b}, true
}

// An insn describes the operand types of an x86 instruction: In is the
// type of its (vector) inputs, Out of its result.
type insn struct {
	In, Out typ
}

var bwdq = map[byte]int{'B': 8, 'W': 16, 'D': 32, 'Q': 64}

// mnemonics maps x86 mnemonics to their operand types, per the Intel SDM.
// Each pattern's first group, if any, is the element-width letter (B, W,
// D, Q) of both input and result.
var mnemonics = []struct {
	re  *regexp.Regexp
	in  byte // operand kind, or 0 for any
	out byte
}{
	{regexp.MustCompile(`^VP(?:ADD|SUB)S([BW])$`), 's', 's'},   // signed saturation
	{regexp.MustCompile(`^VP(?:ADD|SUB)US([BW])$`), 'u', 'u'},  // unsigned saturation
	{regexp.MustCompile(`^VP(?:MIN|MAX)S([BWDQ])$`), 's', 's'}, // signed compare
	{regexp.MustCompile(`^VP(?:MIN|MAX)U([BWDQ])$`), 'u', 'u'}, // unsigned compare
	{regexp.MustCompile(`^VPCMPGT([BWDQ])$`), 's', 0},          // signed greater-than
	{regexp.MustCompile(`^VPCMP([BWDQ])$`), 's', 0},            // AVX-512 signed compare
	{regexp.MustCompile(`^VPCMPU([BWDQ])$`), 'u', 0},           // AVX-512 unsigned compare
	{regexp.MustCompile(`^VPSRAV?([WDQ])$`), 's', 's'},         // arithmetic shift right
	{regexp.MustCompile(`^VPSRLV?([WDQ])$`), 'u', 'u'},         // logical shift right
	{regexp.MustCompile(`^VPAVG([BW])$`), 'u', 'u'},            // unsigned rounded average
	{regexp.MustCompile(`^VPABS([BWDQ])$`), 's', 0},            // absolute value of signed
	{regexp.MustCompile(`^VPSIGN([BWD])$`), 's', 's'},          //
	{regexp.MustCompile(`^VPMULH(W)$`), 's', 's'},              // signed high multiply
	{regexp.MustCompile(`^VPMULHU(W)$`), 'u', 'u'},             // unsigned high multiply
}

// widening and narrowing instructions, whose input and result widths differ.
var (
	// VPMOVSX<in><out>, VPMOVZX<in><out>: sign/zero extension.
	extendRE = regexp.MustCompile(`^VPMOV([SZ])X([BWD])([WDQ])$`)
	// VPMOV<in><out> (truncate), VPMOVS (signed saturate), VPMOVUS (unsigned saturate).
	narrowRE = regexp.MustCompile(`^VPMOV(S|US|)([WDQ])([BWD])$`)
	// VPACKSS<in><out> (signed to signed), VPACKUS (signed to unsigned).
	packRE = regexp.MustCompile(`^VPACK(SS|US)([WD])([BW])$`)
	// VCVT[T]<in>2<out>[X|Y]: conversions; PS/PD float32/64, [U]DQ int32, [U]QQ int64.
	cvtRE = regexp.MustCompile(`^VCVTT?(PS|PD|U?DQ|U?QQ)2(PS|PD|U?DQ|U?QQ)[XY]?$`)
)

var cvtType = map[string]typ{
	"PS": {'f', 32}, "PD": {'f', 64},
	"DQ": {'s', 32}, "UDQ": {'u', 32},
	"QQ": {'s', 64}, "UQQ": {'u', 64},
}

// describe returns the operand types of the x86 instruction asm.
func describe(asm string) (insn, bool) {
	for _, m := range mnemonics {
		if g := m.re.FindStringSubmatch(asm); g != nil {
			b := bwdq[g[1][0]]
			out := typ{m.out, b}
			if m.out == 0 {
				out = typ{}
			}
			return insn{In: typ{m.in, b}, Out: out}, true
		}
	}
	if g := extendRE.FindStringSubmatch(asm); g != nil {
		k := byte('s')
		if g[1] == "Z" {
			k = 'u'
		}
		return insn{In: typ{k, bwdq[g[2][0]]}, Out: typ{0, bwdq[g[3][0]]}}, true
	}
	if g := narrowRE.FindStringSubmatch(asm); g != nil {
		var k byte
		switch g[1] {
		case "S":
			k = 's'
		case "US":
			k = 'u'
		}
		return insn{In: typ{k, bwdq[g[2][0]]}, Out: typ{k, bwdq[g[3][0]]}}, true
	}
	if g := packRE.FindStringSubmatch(asm); g != nil {
		out := byte('s')
		if g[1] == "US" {
			out = 'u'
		}
		return insn{In: typ{'s', bwdq[g[2][0]]}, Out: typ{out, bwdq[g[3][0]]}}, true
	}
	if g := cvtRE.FindStringSubmatch(asm); g != nil {
		return insn{In: cvtType[g[1]], Out: cvtType[g[2]]}, true
	}
	switch asm {
	case "VPMADDWD": // signed words multiplied, adjacent pairs added to signed dwords
		return insn{In: typ{'s', 16}, Out: typ{'s', 32}}, true
	case "VPMADDUBSW": // unsigned bytes (first source) times signed bytes, saturated to signed words
		return insn{In: typ{'u', 8}, Out: typ{'s', 16}}, true
	case "VPMULDQ": // signed dwords to signed qwords
		return insn{In: typ{'s', 32}, Out: typ{'s', 64}}, true
	case "VPMULUDQ":
		return insn{In: typ{'u', 32}, Out: typ{'u', 64}}, true
	}
	return insn{}, false
}

// checkMnemonics checks the x86 instructions that a lowering of a SIMD
// generic op applies directly to the op's arguments.
func checkMnemonics(pass *analysis.Pass, r *rules.Rule) {
	method, recv, ok := parseGeneric(r.Match.Op.Name)
	if !ok {
		return
	}
	var out typ
	if m := toTypeRE.FindStringSubmatch(method); m != nil {
		b, _ := strconv.Atoi(m[2])
		out = typ{kindOf[m[1]], b}
	}
	args := map[string]bool{}
	for _, a := range r.Match.Args {
		if a.IsVar() {
			args[a.Name] = true
		}
	}
	done := map[string]bool{}
	r.Result.Walk(func(v *rules.Value) bool {
		if v.Op == nil || v.Op.IsGeneric() || done[v.Op.Asm] {
			return true
		}
		direct := v == r.Result && r.Match.Ellipsis
		for _, a := range v.Args {
			direct = direct || a.IsVar() && args[a.Name]
		}
		if !direct {
			return true
		}
		in, ok := describe(v.Op.Asm)
		if !ok || signless(v) {
			return true
		}
		done[v.Op.Asm] = true
		if in.In.conflicts(recv) {
			pass.Reportf(r.Pos, "%s lowers %s on %s elements to %s, which takes %s elements",
				r.Match.Op.Name, method, recv, v.Op.Asm, in.In)
		}
		// Composite lowerings may produce intermediate values of other
		// types, so check the promised result type only at the root.
		if v == r.Result && out != (typ{}) && in.Out.conflicts(out) {
			pass.Reportf(r.Pos, "%s promises %s elements but lowers to %s, which produces %s elements",
				r.Match.Op.Name, out, v.Op.Asm, in.Out)
		}
		return true
	})
}

// signless reports whether v is an AVX-512 integer compare whose
// predicate (imm8 & 7, per the Intel SDM: 0 EQ, 3 FALSE, 4 NE, 7 TRUE)
// does not depend on signedness.
func signless(v *rules.Value) bool {
	if !vpcmpRE.MatchString(v.Op.Asm) {
		return false
	}
	p, err := strconv.ParseInt(v.AuxInt, 0, 64)
	if err != nil {
		return false
	}
	switch p & 7 {
	case 0, 3, 4, 7:
		return true
	}
	return false
}

var vpcmpRE = regexp.MustCompile(`^VPCMPU?[BWDQ]$`)

// parityRE parses names such as MulAddEvenSubOdd.
var parityRE = regexp.MustCompile(`^Mul(Add|Sub)(Even|Odd)(Add|Sub)(Even|Odd)`)

// checkParity checks lowerings of the alternating fused multiply-adds.
// Per the Intel SDM, VFMADDSUB* subtracts in even lanes and adds in odd
// ones; VFMSUBADD* adds in even lanes and subtracts in odd ones.
func checkParity(pass *analysis.Pass, r *rules.Rule) {
	m := parityRE.FindStringSubmatch(r.Match.Op.Name)
	if m == nil || m[2] == m[4] {
		return
	}
	even := m[1]
	if m[2] != "Even" {
		even = m[3]
	}
	r.Result.Walk(func(v *rules.Value) bool {
		if v.Op == nil {
			return true
		}
		var hwEven string
		switch {
		case strings.HasPrefix(v.Op.Asm, "VFMADDSUB"):
			hwEven = "Sub"
		case strings.HasPrefix(v.Op.Asm, "VFMSUBADD"):
			hwEven = "Add"
		default:
			return true
		}
		if hwEven != even {
			want := "VFMSUBADD"
			if even == "Sub" {
				want = "VFMADDSUB"
			}
			pass.Reportf(r.Pos, "%s needs %s in even lanes, but %s does %s in even lanes and %s in odd ones; want %s",
				r.Match.Op.Name, strings.ToLower(even), v.Op.Asm, strings.ToLower(hwEven), strings.ToLower(opposite(hwEven)), want)
		}
		return false
	})
}

func opposite(s string) string {
	if s == "Add" {
		return "Sub"
	}
	return "Add"
}

// typeTokenRE matches element-type tokens in generic op names.
var typeTokenRE = regexp.MustCompile(`(Int|Uint|Float|Mask)\d+(x\d+)?s?`)

// checkCollisions reports SIMD machine ops (with the same aux) that are
// the lowering of generic ops with different names, ignoring element
// types. It looks only at rules in simd*.rules files.
func checkCollisions(pass *analysis.Pass, set *rules.RuleSet) {
	type target struct {
		op     *ops.Op
		auxint string
		aux    string
	}
	byTarget := map[target]map[string][]*rules.Rule{}
	var order []target
	for _, r := range set.Rules {
		if r.IsBlock() || r.Match.Op == nil || !r.Match.Op.IsGeneric() || r.Result == nil || r.Result.Op == nil || r.Result.Op.IsGeneric() {
			continue
		}
		if !strings.HasPrefix(filepath.Base(r.Pos.File), "simd") || !passthrough(r) {
			continue
		}
		t := target{r.Result.Op, r.Result.AuxInt, r.Result.Aux}
		name := typeTokenRE.ReplaceAllString(r.Match.Op.Name, "")
		if byTarget[t] == nil {
			byTarget[t] = map[string][]*rules.Rule{}
			order = append(order, t)
		}
		byTarget[t][name] = append(byTarget[t][name], r)
	}
	for _, t := range order {
		names := byTarget[t]
		if len(names) < 2 {
			continue
		}
		var all []string
		for n := range names {
			all = append(all, n)
		}
		slices.Sort(all)
		for _, n := range all {
			var others []string
			for _, o := range all {
				if o != n {
					rs := names[o]
					others = append(others, fmt.Sprintf("%s (%s:%d)", rs[0].Match.Op.Name, filepath.Base(rs[0].Pos.File), rs[0].Pos.Line))
				}
			}
			for _, r := range names[n] {
				pass.Reportf(r.Pos, "%s is also the lowering of %s; one of them probably names the wrong instruction",
					opText(t.op, t.auxint, t.aux), strings.Join(others, ", "))
			}
		}
	}
}

// passthrough reports whether r's result is a single op applied to
// the match's arguments: (A ...) => (B ...) or (A x y) => (B y x).
func passthrough(r *rules.Rule) bool {
	if r.Match.Ellipsis {
		return r.Result.Ellipsis
	}
	vars := map[string]bool{}
	for _, a := range r.Match.Args {
		if !a.IsVar() {
			return false
		}
		vars[a.Name] = true
	}
	for _, a := range r.Result.Args {
		if !a.IsVar() || !vars[a.Name] {
			return false
		}
	}
	return true
}

func opText(op *ops.Op, auxint, aux string) string {
	s := op.Name
	if auxint != "" {
		s += " [" + auxint + "]"
	}
	if aux != "" {
		s += " {" + aux + "}"
	}
	return s
}

var (
	kopRE      = regexp.MustCompile(`^K(?:AND|ANDN|OR|XOR|XNOR|NOT|MOV|SHIFTL|SHIFTR|ADD)([BWDQ])$`)
	maskConvRE = regexp.MustCompile(`^VPMOV(?:Vec\d+x(\d+)ToM|MToVec\d+x(\d+))$`)
)

// kBits returns the number of mask bits a K-register op operates on.
func kBits(op *ops.Op) int {
	if op == nil {
		return 0
	}
	if m := kopRE.FindStringSubmatch(op.Asm); m != nil {
		return bwdq[m[1][0]]
	}
	return 0
}

// convLanes returns the lane count N of a VPMOVMToVec<E>x<N> or
// VPMOVVec<E>x<N>ToM op.
func convLanes(op *ops.Op) int {
	if op == nil {
		return 0
	}
	m := maskConvRE.FindStringSubmatch(op.Name)
	if m == nil {
		return 0
	}
	n, _ := strconv.Atoi(m[1] + m[2])
	return n
}

// checkKWidth checks K-register ops adjacent to mask conversions in a
// rule's result, and K-register ops whose arguments the match binds
// under a mask conversion.
func checkKWidth(pass *analysis.Pass, r *rules.Rule) {
	lanes := map[string]int{} // match vars bound under a mask conversion
	r.Match.Walk(func(v *rules.Value) bool {
		if n := convLanes(v.Op); n > 0 && len(v.Args) == 1 && v.Args[0].IsVar() {
			lanes[v.Args[0].Name] = n
		}
		return true
	})
	reported := false
	report := func(k *ops.Op, n int, conv string) {
		if !reported {
			pass.Reportf(r.Pos, "%s operates on %d mask bits, but %s has %d lanes; lanes %d-%d are lost", k.Name, kBits(k), conv, n, kBits(k), n-1)
			reported = true
		}
	}
	r.Result.Walk(func(v *rules.Value) bool {
		if n := convLanes(v.Op); n > 0 {
			for _, a := range v.Args {
				if b := kBits(a.Op); b > 0 && b < n {
					report(a.Op, n, v.Op.Name)
				}
			}
		}
		if b := kBits(v.Op); b > 0 {
			for _, a := range v.Args {
				if n := convLanes(a.Op); n > b {
					report(v.Op, n, a.Op.Name)
				}
				if n := lanes[a.Name]; a.IsVar() && n > b {
					report(v.Op, n, fmt.Sprintf("the mask %s", a.Name))
				}
			}
		}
		return true
	})
}

// andNotSlot returns which argument an AMD64 and-not op complements, or
// -1. Codegen in amd64/ssa.go: VPANDN* is emitted by simdV21 as
// VPANDN arg1, arg0, dst, which per the Intel SDM computes ^arg0 & arg1;
// KANDN* is emitted as KANDN arg0, arg1, dst, computing ^arg1 & arg0.
func andNotSlot(op *ops.Op) int {
	if op == nil || op.IsGeneric() || op.Arch.Name != "AMD64" {
		return -1
	}
	switch {
	case op.Asm == "VPANDN" || op.Asm == "VPANDND" || op.Asm == "VPANDNQ":
		return 0
	case strings.HasPrefix(op.Asm, "KANDN"):
		return 1
	}
	return -1
}

// andNotOperands finds the first and-not op in v and returns the
// variables in its complemented and plain operands, looking through
// unary wrappers such as VPMOVMToVec.
func andNotOperands(v *rules.Value) (op *ops.Op, neg, pos string) {
	v.Walk(func(w *rules.Value) bool {
		if op != nil {
			return false
		}
		s := andNotSlot(w.Op)
		if s < 0 || len(w.Args) < 2 {
			return true
		}
		n, p := operandVar(w.Args[s]), operandVar(w.Args[1-s])
		if n != "" && p != "" {
			op, neg, pos = w.Op, n, p
		}
		return false
	})
	return
}

func operandVar(v *rules.Value) string {
	for !v.IsLeaf() {
		if len(v.Args) != 1 {
			return ""
		}
		v = v.Args[0]
	}
	if v.IsVar() {
		return v.Name
	}
	return ""
}

func checkAndNot(pass *analysis.Pass, r *rules.Rule) {
	mop, mneg, mpos := andNotOperands(r.Match)
	if mop == nil {
		return
	}
	rop, rneg, rpos := andNotOperands(r.Result)
	if rop == nil || mneg == rneg {
		return
	}
	if rneg == mpos && rpos == mneg {
		pass.Reportf(r.Pos, "and-not operands swapped: %s complements %s, but %s (which complements its arg%d) complements %s",
			mop.Name, mneg, rop.Name, andNotSlot(rop), rneg)
	}
}
