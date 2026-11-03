package optablelint_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/optablelint"
	"github.com/josharian/unruly/ops"
)

// TestFixture runs the analyzer on synthetic op tables whose definitions
// are in testdata/src/cmd/compile/internal/ssa/_gen.
func TestFixture(t *testing.T) {
	gp := ops.RegMaskOf(0, 1, 2, 3)
	vec := ops.RegMaskOf(16, 17, 18, 19)
	k := ops.RegMaskOf(40, 41)
	amd64 := &ops.Arch{Name: "AMD64", GPRegMask: gp, SIMDRegMask: vec, SIMDMaskRegs: k}
	amd64.Ops = []*ops.Op{
		{Name: "MOVQloadidx8", Scale: 8},
		{Name: "SHRXQloadidx8", Scale: 8, FaultOnNilArg0: true},
		{Name: "ADDLloadidx4", Scale: 4, FaultOnNilArg1: true, ResultInArg0: true},
		{Name: "LoweredMemEq", Call: true, FaultOnNilArg0: true, FaultOnNilArg1: true},
		{Name: "VMOVDQU32Masked512load", FaultOnNilArg0: true,
			Reg: ops.RegInfo{Inputs: []ops.RegMask{gp, k}, Outputs: []ops.RegMask{vec}}},
		{Name: "KMOVQstore", FaultOnNilArg0: true, Reg: ops.RegInfo{Inputs: []ops.RegMask{gp, k}}},
		{Name: "VMINPD128", Asm: "VMINPD", Commutative: true},
		{Name: "VPMINSD128", Asm: "VPMINSD", Commutative: true},
	}
	wasm := &ops.Arch{Name: "Wasm"}
	wasm.Ops = []*ops.Op{
		{Name: "F32x4Pmin", Asm: "F32x4Pmin", Commutative: true},
		{Name: "F32x4Min", Asm: "F32x4Min", Commutative: true},
	}
	runFixture(t, "testdata/src/cmd/compile/internal/ssa/_gen", optablelint.Analyzer, amd64, wasm)
}

// TestHistorical checks fixes of the op tables.
func TestHistorical(t *testing.T) {
	// 287d67e3dd removed faultOnNil from 386's and PPC64's indexed ops.
	// Its rules predate typed rules, so only the op tables are analyzed.
	runRevisionOps(t, "287d67e3dd^", optablelint.Analyzer,
		analysistest.Want{File: "386Ops.go", Line: 301, Message: `ADDLloadidx4 is faultOnNilArg1, but it is indexed: it addresses arg1\+4\*arg2`},
		analysistest.Want{File: "386Ops.go", Line: 389, Message: `ADDLmodifyidx4 is faultOnNilArg0, but it is indexed`},
		analysistest.Want{File: "PPC64Ops.go", Line: 312, Message: `MOVDloadidx is faultOnNilArg0, but it is indexed`},
	)
	runRevisionOps(t, "287d67e3dd", optablelint.Analyzer,
		analysistest.Want{File: "386Ops.go", Line: 301, Absent: true},
		analysistest.Want{File: "386Ops.go", Line: 389, Absent: true},
		analysistest.Want{File: "PPC64Ops.go", Line: 313, Absent: true},
	)

	// c7aa83bdd2 made AMD64's floating-point SIMD min and max non-commutative.
	analysistest.RunRevision(t, "c7aa83bdd2^", optablelint.Analyzer,
		analysistest.Want{File: "simdAMD64ops.go", Line: 225, Message: `VMAXPD128 is commutative, but VMAXPD returns its second operand`},
	)
	analysistest.RunRevision(t, "c7aa83bdd2", optablelint.Analyzer,
		analysistest.Want{File: "simdAMD64ops.go", Line: 225, Absent: true},
	)
}

// TestLive pins the defects in the op tables at aa94415944 (October 2026),
// none of which is fixed there.
func TestLive(t *testing.T) {
	analysistest.RunRevision(t, "aa94415944", optablelint.Analyzer,
		analysistest.Want{File: "AMD64Ops.go", Line: 1362, Message: `SHRXQloadidx8 is faultOnNilArg0, but it is indexed.*no rule produces it; ssacompile/addressingmodes.go refers to it`},
		analysistest.Want{File: "ARM64Ops.go", Line: 586, Message: `LoweredMemEq is faultOnNilArg0 and faultOnNilArg1, but it is a call, and the callee.*produced by ARM64.rules:466`},
		analysistest.Want{File: "AMD64Ops.go", Line: 1430, Message: `VPMASK32store128 is faultOnNilArg0, but its memory access is masked.*produced by AMD64.rules:1758`},
		analysistest.Want{File: "AMD64Ops.go", Line: 1447, Message: `VPMASK64store512 is faultOnNilArg0, but its memory access is masked`},
		analysistest.Want{File: "ARM64Ops.go", Line: 925, Message: `ZST1BPredstore is faultOnNilArg0, but its memory access is masked`},
		analysistest.Want{File: "simdWasmops.go", Line: 14, Message: `F32x4Pmin is commutative.*latent`},
		// KMOVQstore stores a mask register; the mask is data, not a predicate.
		analysistest.Want{File: "AMD64Ops.go", Line: 1526, Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, optablelint.Analyzer)
}
