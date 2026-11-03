// Package optablelint checks machine op tables (the *Ops.go files) for
// flags that promise more than the instruction delivers.
package optablelint

import (
	"fmt"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "optablelint",
	Doc: `report op table flags that the instruction does not honor

faultOnNilArgN promises that the op faults whenever argN is nil.
nilcheckelim relies on it to delete an explicit nil check that precedes the
op in the same block, so the op must dereference argN at a small offset
unconditionally. That is false for:

  - indexed ops, which address arg0+scale*arg1+off: with arg0 == nil and
    a large arg1 the access lands in mapped memory. For example, with
    AMD64's SHRXQloadidx8, p[i&(1<<30-1)] >> (s&63) with p == nil reads
    address 8*i instead of panicking (GOAMD64=v3).
  - calls, whose callee decides what to touch. ARM64's LoweredMemEq calls
    runtime.memequal, which returns true without loading when the
    pointers are equal, so *p == *q with p == q == nil is true instead of
    a nil dereference panic.
  - masked or predicated memory ops (AVX VMASKMOV, AVX-512 {k} masking,
    SVE predication), which suppress faults in masked-off elements: with
    an all-false mask, x.StoreArrayMasked(&p.a, m) and p == nil does not
    panic.

commutative lets CSE merge op(a, b) with op(b, a) and lets rulegen match
either order. It is wrong for operations that pick an operand on ties or
NaNs: x86 (V)MIN/MAX{SS,SD,PS,PD,SH,PH} return the second operand if either
is NaN or both are zero (Intel SDM; see also the MINSD comment in
AMD64.rules), and WebAssembly's pmin(a, b) is b < a ? b : a.

Diagnostics are reported at the op's definition and say what produces the
op: a rule, other compiler code, or nothing (a latent defect).`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	genDir := genDir(pass)
	refs := &opRefs{compileDir: filepath.Join(genDir, "..", "..")}
	for _, a := range arches(pass) {
		defs := opDefs(genDir, a.Name)
		producers := producers(pass, a)
		maskedMem := maskedMemOps(pass, a)
		for _, op := range a.Ops {
			pos, ok := defs[op.Name]
			if !ok {
				continue
			}
			report := func(format string, args ...any) {
				msg := fmt.Sprintf(format, args...)
				if r := producers[op]; r != nil {
					msg += fmt.Sprintf(" (produced by %s:%d)", filepath.Base(r.Pos.File), r.Pos.Line)
				} else if f := refs.find(op); f != "" {
					msg += fmt.Sprintf(" (no rule produces it; %s refers to it)", f)
				} else {
					msg += " (latent: nothing produces it)"
				}
				pass.Report(pos, msg)
			}
			checkFaultOnNil(a, op, maskedMem[op], report)
			checkCommutative(a, op, report)
		}
	}
	return nil
}

// idxScaleRE matches the scale in the name of an indexed op without a
// scale field, such as 386's ADDLloadidx4.
var idxScaleRE = regexp.MustCompile(`idx([1248])`)

func checkFaultOnNil(a *ops.Arch, op *ops.Op, maskedMem bool, report func(string, ...any)) {
	var args []string
	if op.FaultOnNilArg0 {
		args = append(args, "faultOnNilArg0")
	}
	if op.FaultOnNilArg1 {
		args = append(args, "faultOnNilArg1")
	}
	if len(args) == 0 {
		return
	}
	flag := strings.Join(args, " and ")
	const consequence = "nilcheckelim deletes a nil check the op does not perform"
	switch {
	case op.Scale != 0 || strings.Contains(strings.ToLower(op.Name), "idx"):
		scale := ""
		if op.Scale > 1 {
			scale = fmt.Sprintf("%d*", op.Scale)
		} else if m := idxScaleRE.FindStringSubmatch(op.Name); m != nil && m[1] != "1" {
			scale = m[1] + "*"
		}
		base := 0
		if !op.FaultOnNilArg0 {
			base = 1
		}
		report("%s is %s, but it is indexed: it addresses arg%d+%sarg%d+off, which is mapped memory for a nil arg%d and a large index, so %s", op.Name, flag, base, scale, base+1, base, consequence)
	case op.Call:
		report("%s is %s, but it is a call, and the callee need not dereference its arguments (runtime.memequal, for one, returns true without loading when the pointers are equal or the size is 0), so %s", op.Name, flag, consequence)
	case maskedMem || hasMaskInput(a, op):
		report("%s is %s, but its memory access is masked: masked-off elements do not fault, so with an all-false mask %s", op.Name, flag, consequence)
	}
}

// hasMaskInput reports whether op's vector data is governed by an
// argument in a SIMD mask or predicate register (AVX-512 K, SVE P): op takes
// such an argument and also has a vector input or output. (KMOVBstore and
// SVE's PSTRstore have a mask input too, but it is the data stored.)
func hasMaskInput(a *ops.Arch, op *ops.Op) bool {
	if a.SIMDMaskRegs.Empty() {
		return false
	}
	isMask := func(m ops.RegMask) bool { return !m.Empty() && m.SubsetOf(a.SIMDMaskRegs) }
	isVec := func(m ops.RegMask) bool {
		return !m.Intersect(a.SIMDRegMask.Minus(a.SIMDMaskRegs)).Empty()
	}
	var mask, vec bool
	for _, in := range op.Reg.Inputs {
		mask = mask || isMask(in)
		vec = vec || isVec(in)
	}
	for _, out := range op.Reg.Outputs {
		vec = vec || isVec(out)
	}
	return mask && vec
}

// maskedMemOps returns the machine ops that a's rules lower the generic
// masked memory ops (LoadMaskedN, StoreMaskedN) to. Their mask need not be
// in a mask register: AVX VMASKMOV takes it in a vector register.
func maskedMemOps(pass *analysis.Pass, a *ops.Arch) map[*ops.Op]bool {
	m := make(map[*ops.Op]bool)
	for _, s := range pass.Sets {
		if s.Arch != a {
			continue
		}
		for _, r := range s.Rules {
			if r.Match == nil || r.Result == nil || r.Match.Op == nil || r.Result.Op == nil {
				continue
			}
			g := r.Match.Op
			if !g.IsGeneric() || !(strings.HasPrefix(g.Name, "LoadMasked") || strings.HasPrefix(g.Name, "StoreMasked")) {
				continue
			}
			if !r.Result.Op.IsGeneric() {
				m[r.Result.Op] = true
			}
		}
	}
	return m
}

// nonCommutative matches the asm of ops whose result depends on operand
// order although the operation looks symmetric, by arch.
var nonCommutative = map[string]*regexp.Regexp{
	// Intel SDM, MINPS/MAXPS/...: "If the values being compared are both
	// 0.0s (of either sign), the value in the second operand (source
	// operand) is returned. If only one value is a NaN (SNaN or QNaN) for
	// this instruction, the second operand (source operand), either a NaN
	// or a valid floating-point value, is written to the result."
	// AMD64.rules lowers Min64F with this in mind; genericOps.go's
	// Min64FSel (arg0 < arg1 ? arg0 : arg1) lowers to MINSD.
	"386":   regexp.MustCompile(`^V?(MIN|MAX)(SS|SD|PS|PD|SH|PH)$`),
	"AMD64": regexp.MustCompile(`^V?(MIN|MAX)(SS|SD|PS|PD|SH|PH)$`),
	// WebAssembly SIMD: pmin(z1, z2) = z2 < z1 ? z2 : z1, and
	// pmax(z1, z2) = z1 < z2 ? z2 : z1.
	"Wasm": regexp.MustCompile(`^F(32x4|64x2)P(min|max)$`),
}

func checkCommutative(a *ops.Arch, op *ops.Op, report func(string, ...any)) {
	if !op.Commutative {
		return
	}
	re := nonCommutative[a.Name]
	if re == nil || !re.MatchString(op.Asm) {
		return
	}
	var why string
	switch {
	case a.Name == "Wasm" && strings.HasSuffix(op.Asm, "min"):
		why = "computes pmin(a, b) = b < a ? b : a, so pmin(NaN, 1) is NaN but pmin(1, NaN) is 1"
	case a.Name == "Wasm":
		why = "computes pmax(a, b) = a < b ? b : a, so pmax(NaN, 1) is NaN but pmax(1, NaN) is 1"
	default:
		why = "returns its second operand if either is NaN or both are zero, so it maps (NaN, 1) to 1 but (1, NaN) to NaN, and (-0, +0) to +0 but (+0, -0) to -0"
	}
	report("%s is commutative, but %s %s; CSE may merge op(a, b) with op(b, a)", op.Name, op.Asm, why)
}

// arches returns the machine arches of the rule sets being analyzed.
func arches(pass *analysis.Pass) []*ops.Arch {
	var as []*ops.Arch
	seen := make(map[*ops.Arch]bool)
	for _, s := range pass.Sets {
		if a := s.Arch; !a.Generic && !seen[a] {
			seen[a] = true
			as = append(as, a)
		}
	}
	return as
}

// producers maps each op of a to the first rule whose result produces it.
func producers(pass *analysis.Pass, a *ops.Arch) map[*ops.Op]*rules.Rule {
	m := make(map[*ops.Op]*rules.Rule)
	for _, s := range pass.Sets {
		if s.Arch != a {
			continue
		}
		for _, r := range s.Rules {
			for _, v := range r.ResultValues() {
				v.Walk(func(v *rules.Value) bool {
					if v.Op != nil && m[v.Op] == nil {
						m[v.Op] = r
					}
					return true
				})
			}
		}
	}
	return m
}

// genDir returns the _gen directory being analyzed. It prefers the
// directory of the rules files to pass.Ops.Dir, because ops.Load shares
// tables (and their Dir) between trees with identical _gen Go sources.
func genDir(pass *analysis.Pass) string {
	for _, s := range pass.Sets {
		for _, f := range s.Files {
			return filepath.Dir(f.Path)
		}
	}
	return pass.Ops.Dir
}
