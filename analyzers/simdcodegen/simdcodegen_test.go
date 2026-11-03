package simdcodegen_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/simdcodegen"
	"github.com/josharian/unruly/ops"
)

// TestFixture runs the analyzer on synthetic op tables whose definitions
// are in testdata/src/cmd/compile/internal/ssa/_gen and whose codegen is in
// testdata/src/cmd/compile/internal/amd64.
func TestFixture(t *testing.T) {
	gp := ops.RegMaskOf(0, 1, 2, 3)
	vec := ops.RegMaskOf(16, 17, 18, 19)
	k := ops.RegMaskOf(40, 41)
	v11 := ops.RegInfo{Inputs: []ops.RegMask{vec}, Outputs: []ops.RegMask{vec}}
	v21 := ops.RegInfo{Inputs: []ops.RegMask{vec, vec}, Outputs: []ops.RegMask{vec}}
	v2kv := ops.RegInfo{Inputs: []ops.RegMask{vec, vec, k}, Outputs: []ops.RegMask{vec}}
	vkv := ops.RegInfo{Inputs: []ops.RegMask{vec, k}, Outputs: []ops.RegMask{vec}}
	amd64 := &ops.Arch{Name: "AMD64", GPRegMask: gp, SIMDRegMask: vec, SIMDMaskRegs: k}
	amd64.Ops = []*ops.Op{
		{Name: "VPSLLD512const", ArgLength: 1, Aux: "UInt8", Reg: v11},
		{Name: "VPSLLDMasked512constMerging", ArgLength: 3, Aux: "UInt8", ResultInArg0: true, Reg: v2kv},
		{Name: "VPADDD512", ArgLength: 2, Reg: v21},
		{Name: "VPSHUFD512load", ArgLength: 2, Aux: "SymValAndOff",
			Reg: ops.RegInfo{Inputs: []ops.RegMask{gp}, Outputs: []ops.RegMask{vec}}},
		{Name: "VPSUBD512", ArgLength: 2, Reg: v21},
		{Name: "VPABSD512", ArgLength: 1, Reg: v11},
		{Name: "VPADDDMasked512", ArgLength: 3, Reg: v2kv},
		{Name: "VPADDDMasked512Merging", ArgLength: 3, ResultInArg0: true, Reg: v2kv},
		{Name: "VPBLENDMDMasked512", Asm: "VPBLENDMD", ArgLength: 3, Reg: v2kv},
		{Name: "VPABSDMasked512", ArgLength: 2, Reg: vkv},
		{Name: "VPEXTRD128", ArgLength: 1, Aux: "UInt8", Reg: v11},
		{Name: "VPMISSING512", ArgLength: 1, Reg: v11},
	}
	runFixture(t, "testdata/src/cmd/compile/internal/ssa/_gen", simdcodegen.Analyzer, amd64)
}

// TestIntroduced checks the commit that introduced AMD64's masked merging
// ops, whose immediate forms drop the immediate (not fixed as of
// aa94415944).
func TestIntroduced(t *testing.T) {
	analysistest.RunRevision(t, "86b4fe31d9^", simdcodegen.Analyzer)
	analysistest.RunRevision(t, "86b4fe31d9", simdcodegen.Analyzer,
		analysistest.Want{File: "simdAMD64ops.go", Line: 2303, Message: `VPSLLDMasked512constMerging has aux UInt8, but its codegen at simdssa.go:\d+ \(simdV2kvResultInArg0\) never reads`},
	)
}

// TestLive pins the defects at aa94415944 (October 2026).
func TestLive(t *testing.T) {
	diags := analysistest.RunRevision(t, "aa94415944", simdcodegen.Analyzer,
		analysistest.Want{File: "simdAMD64ops.go", Line: 3086, Message: `VPSLLDMasked512constMerging has aux UInt8, but its codegen at simdssa.go:2939 \(simdV2kvResultInArg0\) never reads v.AuxInt or v.Aux: the immediate is dropped \(produced by simdAMD64.rules:2076\)`},
		analysistest.Want{File: "simdAMD64ops.go", Line: 3119, Message: `VRNDSCALEPDMasked512Merging has aux UInt8`},
		// The zeroing-masked form reads its immediate.
		analysistest.Want{File: "simdAMD64ops.go", Line: 1410, Absent: true},
	)
	if len(diags) != 60 {
		t.Errorf("got %d diagnostics at aa94415944, want 60 (the imm8 Merging ops)", len(diags))
	}
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, simdcodegen.Analyzer)
}
