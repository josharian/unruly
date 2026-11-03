// Package simdmaskshape checks the vector shapes and mask granularity of
// AMD64 SIMD rules.
package simdmaskshape

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "simdmaskshape",
	Doc: `check vector widths and mask granularity of AMD64 SIMD rules

An AVX-512 write mask has one bit per destination element, so the same
K register means different lanes to ops with different element widths.
simdAMD64.rules fuses a masking wrapper around an unmasked op into the
op's masked form:

	(VMOVDQU32Masked128 (OP x) mask)       => (OPMasked128 x mask)
	(VPBLENDMDMasked512 dst (OP x) mask)   => (OPMasked512Merging dst x mask)
	(VPBLENDVB128 dst (OP x) mask)         => (OPMasked128Merging dst x (VPMOVVec32x4ToM mask))

These are sound only if the wrapper's lanes are OP's output elements.
For example, VPMADDWD multiplies 16-bit lanes and writes 32-bit ones, so in

	(VPBLENDVB128 dst (VPMADDWD128 x y) mask) => (VPMADDWDMasked128Merging dst x y (VPMOVVec16x8ToM mask))

x.DotProductPairs(y).IfElse(m, z) with m a Mask32x4 selects result
element i by m[i/2]. The checks:

  - Width: OP's result width must be the wrapper's, or the rule can never
    match well-typed SSA.
  - Granularity: VMOVDQU<E>Masked and VPBLENDM<B|W|D|Q> select E-bit lanes,
    so E must be OP's output element width. VPBLENDVB selects bytes (archsimd's
    IfElse uses it for every 128- and 256-bit type, including after
    AsInt8x16), so a fusion through VPMOVVec<E>ToM is sound only for E=8;
    and E must be OP's output element width even for masks of OP's type.
  - Coverage: a merging fusion requires OP to write every output element.
    A narrowing op such as VPMOVDB (Int32x4 to the low 4 bytes of an
    Int8x16) zeroes the rest even under merge masking.
  - Lowering shapes: a generic op's Go result width must equal the typ of
    the machine op it lowers to, and the VPMOVVec<E>x<N>ToM and
    VPMOVMToVec<E>x<N> mask conversions in lowerings must match the
    archsimd Mask types of the method's mask argument and result.

OP's output element width comes from the archsimd methods that the
compiler intrinsifies as the generic ops lowered to OP (and to other ops
with the same asm and typ); ops whose methods disagree, such as bitwise
ops, are not checked for granularity.`,
	Run: run,
}

type wrapperKind int

const (
	notWrapper   wrapperKind = iota
	zeroWrapper              // VMOVDQU<E>Masked: lane i = k[i] ? x[i] : 0
	mergeWrapper             // VPBLENDM<X>Masked: lane i = k[i] ? arg1[i] : arg0[i]
	byteBlend                // VPBLENDVB: byte j = msb(arg2.byte[j]) ? arg1[j] : arg0[j]
)

var (
	movdquRE  = regexp.MustCompile(`^VMOVDQU(8|16|32|64)$`)
	blendmRE  = regexp.MustCompile(`^VPBLENDM([BWDQ])$`)
	vec2mRE   = regexp.MustCompile(`^VPMOV([BWDQ])2M$`) // VPMOVVec<E>x<N>ToM
	m2vecRE   = regexp.MustCompile(`^VPMOVM2([BWDQ])$`) // VPMOVMToVec<E>x<N>
	maskOpRE  = regexp.MustCompile(`^VPMOV(?:Vec(\d+)x(\d+)ToM|MToVec(\d+)x(\d+))$`)
	bwdqWidth = map[string]int{"B": 8, "W": 16, "D": 32, "Q": 64}
)

// wrapper classifies op as a masking wrapper and returns its lane width.
// The semantics are those of the instructions in the Intel SDM, with
// operand order from amd64/ssa.go: VPBLENDM* is emitted by simdV2kv
// (VPBLENDMD arg1, arg0, K(arg2)) and VPBLENDVB by simdV31 (VPBLENDVB
// arg2, arg1, arg0).
func wrapper(op *ops.Op) (wrapperKind, int) {
	if op == nil || op.IsGeneric() || !strings.HasPrefix(op.Typ, "Vec") {
		return notWrapper, 0
	}
	if m := movdquRE.FindStringSubmatch(op.Asm); m != nil && op.ArgLength == 2 && maskArg(op) == 1 {
		e, _ := strconv.Atoi(m[1])
		return zeroWrapper, e
	}
	if m := blendmRE.FindStringSubmatch(op.Asm); m != nil && op.ArgLength == 3 && maskArg(op) == 2 {
		return mergeWrapper, bwdqWidth[m[1]]
	}
	if op.Asm == "VPBLENDVB" && op.ArgLength == 3 {
		return byteBlend, 8
	}
	return notWrapper, 0
}

// maskArg returns the index of op's mask-register (AVX-512 K register)
// argument, or -1.
func maskArg(op *ops.Op) int {
	k := maskRegs(op.Arch)
	for i, in := range op.Reg.Inputs {
		if !in.Empty() && !k.Empty() && in.Minus(k).Empty() {
			return i
		}
	}
	return -1
}

// maskRegs returns a's SIMD mask registers. Trees before the
// simdmaskreg arch field (October 2026) don't declare them; there, they
// are the registers named K0-K7.
func maskRegs(a *ops.Arch) ops.RegMask {
	if !a.SIMDMaskRegs.Empty() {
		return a.SIMDMaskRegs
	}
	var m ops.RegMask
	for i, name := range a.RegNames {
		if len(name) == 2 && name[0] == 'K' && '0' <= name[1] && name[1] <= '7' {
			m = m.Add(i)
		}
	}
	return m
}

// vecBits returns the width of a "Vec128"-style op typ, or 0.
func vecBits(typ string) int {
	n, err := strconv.Atoi(strings.TrimPrefix(typ, "Vec"))
	if err != nil || !strings.HasPrefix(typ, "Vec") {
		return 0
	}
	return n
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		if set.Arch.Name != "AMD64" || set.Suffix != "" {
			continue
		}
		c := newChecker(pass, set)
		for _, r := range set.Rules {
			if r.IsBlock() || r.Match.Op == nil {
				continue
			}
			if r.Match.Op.IsGeneric() {
				c.checkLowering(r)
			} else {
				c.checkFusion(r)
			}
		}
	}
	return nil
}

type checker struct {
	pass *analysis.Pass
	api  map[string][]*goSig // by generic op name

	// sigs are the archsimd methods whose generic ops lower to each
	// machine op (by name).
	sigs map[string][]*goSig
	// elems are the output element widths of the archsimd results of
	// generic ops lowered to ops with each asm and typ.
	elems map[string]map[int]bool
}

func newChecker(pass *analysis.Pass, set *rules.RuleSet) *checker {
	c := &checker{
		pass:  pass,
		api:   loadGoAPI(pass.Ops.Dir, set.Arch.Name),
		sigs:  map[string][]*goSig{},
		elems: map[string]map[int]bool{},
	}
	for _, r := range set.Rules {
		if r.IsBlock() || r.Match.Op == nil || !r.Match.Op.IsGeneric() || r.Result == nil || r.Result.Op == nil || r.Result.Op.IsGeneric() {
			continue
		}
		m := r.Result.Op
		for _, g := range c.api[r.Match.Op.Name] {
			out, ok := parseShape(g.Result)
			if !ok || out.Kind == "Mask" {
				continue
			}
			c.sigs[m.Name] = append(c.sigs[m.Name], g)
			k := insnKey(m)
			if c.elems[k] == nil {
				c.elems[k] = map[int]bool{}
			}
			c.elems[k][out.Elem] = true
		}
	}
	return c
}

// outElem returns the output element width of op, if all archsimd methods
// lowered to an op with op's asm and typ agree on it.
func (c *checker) outElem(op *ops.Op) (int, bool) {
	es := c.elems[insnKey(op)]
	if len(es) != 1 {
		return 0, false
	}
	for e := range es {
		return e, true
	}
	panic("unreachable")
}

// insnKey identifies op's instruction and result width. Ops with the
// same key (VPSLLD512, VPSLLD512const, VPSLLDMasked512, ...) produce the
// same kind of elements.
func insnKey(op *ops.Op) string {
	if op.Asm == "" {
		return op.Name
	}
	return op.Asm + "/" + op.Typ
}

// example returns a method lowered to op, for diagnostics.
func (c *checker) example(op *ops.Op) *goSig {
	if s := c.sigs[op.Name]; len(s) > 0 {
		return s[0]
	}
	return nil
}

// partial reports whether op writes only some of its output elements:
// every method lowered to it narrows a single vector argument to a
// result with more, narrower lanes (such as Int32x4.TruncToInt8, which
// returns an Int8x16 with 4 meaningful lanes). It returns the number of
// elements written and the result's lane count.
func (c *checker) partial(op *ops.Op) (written, lanes int, ok bool) {
	sigs := c.sigs[op.Name]
	if len(sigs) == 0 {
		return 0, 0, false
	}
	for i, g := range sigs {
		out, _ := parseShape(g.Result)
		var in shape
		n := 0
		for _, a := range g.Args {
			if s, ok := parseShape(a); ok && s.Kind != "Mask" {
				in = s
				n++
			}
		}
		if n != 1 || in.Elem <= out.Elem || in.Lanes >= out.Lanes {
			return 0, 0, false
		}
		if i > 0 && (in.Lanes != written || out.Lanes != lanes) {
			return 0, 0, false
		}
		written, lanes = in.Lanes, out.Lanes
	}
	return written, lanes, true
}

func (c *checker) checkFusion(r *rules.Rule) {
	kind, we := wrapper(r.Match.Op)
	if kind == notWrapper || r.Result == nil || r.Result.Op == nil {
		return
	}
	dataIdx, maskIdx := 0, 1
	if kind != zeroWrapper {
		dataIdx, maskIdx = 1, 2
	}
	if len(r.Match.Args) <= maskIdx {
		return
	}
	inner := r.Match.Args[dataIdx]
	if inner.Op == nil || inner.Op.IsGeneric() {
		return
	}
	fused := r.Result.Op
	if fused.IsGeneric() || maskArg(fused) < 0 {
		return // not a fusion into a masked op
	}
	w := r.Match.Op
	ww, iw := vecBits(w.Typ), vecBits(inner.Op.Typ)
	if ww == 0 || iw == 0 {
		return
	}
	if ww != iw {
		c.pass.Reportf(r.Pos, "never matches: %s operates on Vec%d but %s produces Vec%d, so no well-typed value matches (and %s would be ill-typed)",
			w.Name, ww, inner.Op.Name, iw, fused.Name)
		return
	}

	eOut, known := c.outElem(inner.Op)
	ex := c.example(inner.Op)
	var probs []string

	switch kind {
	case zeroWrapper, mergeWrapper:
		if known && eOut != we {
			p := fmt.Sprintf("mask granularity: %s selects %d-bit lanes, but %s writes %d-bit elements%s, so %s masks per %d-bit element",
				w.Name, we, inner.Op.Asm, eOut, resultNote(ex), fused.Name, eOut)
			if ex != nil {
				use := ".Masked(m)"
				if kind == mergeWrapper {
					use = ".IfElse(m, z)"
				}
				p += fmt.Sprintf(": %s.AsInt%dx%d()%s selects %d-bit element i by m[%s]", call(ex), we, ww/we, use, eOut,
					lanes(ww/eOut, func(i int) int { return below(i, ww/we) }))
				if eOut < we {
					p += fmt.Sprintf(" instead of m[%s]", lanes(ww/eOut, func(i int) int { return i * eOut / we }))
				} else {
					p += fmt.Sprintf(" instead of masking each %d-bit lane j by m[j]", we)
				}
				p = withNoLane(p)
			}
			probs = append(probs, p)
		}
	case byteBlend:
		conv := findMaskConv(r.Result, r.Match.Args[maskIdx])
		if conv == nil {
			break
		}
		m := vec2mRE.FindStringSubmatch(conv.Asm)
		ec := bwdqWidth[m[1]]
		if known && ec != eOut {
			p := fmt.Sprintf("mask granularity: %s writes %d-bit elements%s, but the fused %s takes its mask from %s, which keeps one bit per %d-bit lane",
				inner.Op.Asm, eOut, resultNote(ex), fused.Name, conv.Name, ec)
			if ex != nil {
				p += fmt.Sprintf(": %s.IfElse(m, z) with m a Mask%dx%d selects element i by m[%s] instead of m[%s]",
					call(ex), eOut, ww/eOut,
					lanes(ww/eOut, func(i int) int {
						if below(i, ww/ec) < 0 {
							return -1
						}
						return ((i+1)*ec - 1) / eOut
					}),
					lanes(ww/eOut, func(i int) int { return i }))
				p = withNoLane(p)
			}
			probs = append(probs, p)
		} else if ec != 8 {
			p := fmt.Sprintf("mask granularity: VPBLENDVB selects bytes, but %s keeps only the top bit of each %d-bit lane of the mask, so %s blends whole %d-bit elements",
				conv.Name, ec, fused.Name, ec)
			if ex != nil {
				p += fmt.Sprintf(": %s.AsInt8x%d().IfElse(m, z) with a Mask8x%d m ignores all but m[%d] of each %d bytes",
					call(ex), ww/8, ww/8, ec/8-1, ec/8)
			}
			probs = append(probs, p)
		}
	}

	if kind != zeroWrapper {
		if written, n, ok := c.partial(inner.Op); ok {
			p := fmt.Sprintf("merge coverage: %s writes only %d of its %d result elements and zeroes the rest even under merge masking, so %s loses dst in elements %d..%d",
				inner.Op.Asm, written, n, fused.Name, written, n-1)
			if ex != nil {
				p += fmt.Sprintf(" (%s.IfElse(m, z) must keep z there)", call(ex))
			}
			probs = append(probs, p)
		}
	}
	if len(probs) > 0 {
		c.pass.Reportf(r.Pos, "%s", strings.Join(probs, "; "))
	}
}

// findMaskConv returns the VPMOVVec<E>x<N>ToM op in res applied to the
// match's mask argument m (a variable), or nil.
func findMaskConv(res, m *rules.Value) *ops.Op {
	if !m.IsVar() {
		return nil
	}
	var conv *ops.Op
	res.Walk(func(v *rules.Value) bool {
		if v.Op != nil && vec2mRE.MatchString(v.Op.Asm) && len(v.Args) == 1 && v.Args[0].IsLeaf() && v.Args[0].Name == m.Name {
			conv = v.Op
		}
		return conv == nil
	})
	return conv
}

// withNoLane explains a "-" from lanes in p, if any.
func withNoLane(p string) string {
	if strings.Contains(p, "[-") || strings.Contains(p, " -") {
		p += " (-: no lane of m)"
	}
	return p
}

// below returns i if i < n, else -1.
func below(i, n int) int {
	if i < n {
		return i
	}
	return -1
}

func resultNote(g *goSig) string {
	if g == nil {
		return ""
	}
	return fmt.Sprintf(" (%s returns %s)", g.Method, g.Result)
}

func call(g *goSig) string {
	_, name, _ := strings.Cut(g.Method, ".")
	if len(g.Args) > 1 {
		return "x." + name + "(...)"
	}
	return "x." + name + "()"
}

// lanes formats f(i) for i in [0, n) as a space-separated list, writing
// "-" for negative values; it abbreviates long lists.
func lanes(n int, f func(int) int) string {
	var s []string
	for i := range min(n, 8) {
		if j := f(i); j >= 0 {
			s = append(s, strconv.Itoa(j))
		} else {
			s = append(s, "-")
		}
	}
	if n > 8 {
		s = append(s, "...")
	}
	return strings.Join(s, " ")
}

func (c *checker) checkLowering(r *rules.Rule) {
	sigs := c.api[r.Match.Op.Name]
	if len(sigs) == 0 || r.Result == nil || r.Result.Op == nil || r.Result.Op.IsGeneric() {
		return
	}
	res := r.Result.Op
	g := sigs[0]
	for _, s := range sigs[1:] {
		if s.Result != g.Result {
			return // ambiguous, e.g. Mask8x16.AndNot and Int32x4.AndNot share AndNotInt32x4
		}
	}
	out, ok := parseShape(g.Result)
	if !ok {
		return
	}
	if b := vecBits(res.Typ); b != 0 && out.Kind != "Mask" && b != out.Bits() {
		c.pass.Reportf(r.Pos, "lowering shape: %s returns %s (%d bits), but %s produces %s", g.Method, g.Result, out.Bits(), res.Name, res.Typ)
	}
	// maskOut: (G ...) => (VPMOVMToVec<E>x<N> ...) must produce G's Mask result type.
	if m := maskOpRE.FindStringSubmatch(res.Name); m != nil && m[3] != "" && m2vecRE.MatchString(res.Asm) {
		want := "Mask" + m[3] + "x" + m[4]
		if g.Result != want {
			c.pass.Reportf(r.Pos, "lowering shape: %s returns %s, but the result is converted from a K mask by %s, which produces a %s", g.Method, g.Result, res.Name, want)
		}
	}
	// maskIn: a VPMOVVec<E>x<N>ToM applied to the generic op's argument j
	// must match the Go type of argument j.
	argIdx := map[string]int{}
	for j, a := range r.Match.Args {
		if a.IsVar() {
			argIdx[a.Name] = j
		}
	}
	r.Result.Walk(func(v *rules.Value) bool {
		if v.Op == nil || len(v.Args) != 1 || !v.Args[0].IsVar() || !vec2mRE.MatchString(v.Op.Asm) {
			return true
		}
		m := maskOpRE.FindStringSubmatch(v.Op.Name)
		if m == nil || m[1] == "" {
			return true
		}
		j, ok := argIdx[v.Args[0].Name]
		if !ok {
			return true
		}
		have := "Mask" + m[1] + "x" + m[2]
		for _, s := range sigs {
			t := s.goArg(j)
			if t == "" {
				continue
			}
			if t != have {
				c.pass.Reportf(r.Pos, "lowering shape: %s converts argument %s (Go type %s) to a K mask with %s, which expects a %s", s.Method, v.Args[0].Name, t, v.Op.Name, have)
				return false
			}
		}
		return true
	})
}
