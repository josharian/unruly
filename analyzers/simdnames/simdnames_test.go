package simdnames_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/simdnames"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", simdnames.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, simdnames.Analyzer)
}

func TestHistorical(t *testing.T) {
	type W = analysistest.Want
	cases := []struct {
		rev         string
		buggy, good W
	}{
		// SHA256Message2 lowered to SHA256MSG1.
		{"d3a0321dba",
			W{File: "simdAMD64.rules", Rule: "(SHA256Message2Uint32x4 ...) => (SHA256MSG1128 ...)", Message: "SHA256MSG1128 is also the lowering of SHA256Message1Uint32x4"},
			W{File: "simdAMD64.rules", Rule: "(SHA256Message2Uint32x4 ...) => (SHA256MSG2128 ...)"}},
		// Unsigned saturation lowered to signed saturating narrows.
		{"baa0ae3aaa",
			W{File: "simdAMD64.rules", Rule: "(SaturateToUint8Int16x8 ...) => (VPMOVSWB128_128 ...)", Message: "promises unsigned 8-bit elements but lowers to VPMOVSWB, which produces signed 8-bit elements"},
			W{File: "simdAMD64.rules", Rule: "(SaturateToUint8Uint16x8 ...) => (VPMOVUSWB128_128 ...)"}},
		// VPACKUSDW reads signed inputs.
		{"42cda7c1df",
			W{File: "simdAMD64.rules", Rule: "(SaturateToUint16ConcatUint32x4 ...) => (VPACKUSDW128 ...)", Message: "on unsigned 32-bit elements to VPACKUSDW, which takes signed 32-bit elements"},
			W{File: "simdAMD64.rules", Rule: "(SaturateToUint16ConcatInt32x4 ...) => (VPACKUSDW128 ...)"}},
		// Unsigned saturating add lowered to the signed instruction.
		{"8eb5f6020e",
			W{File: "simdAMD64.rules", Rule: "(AddSaturatedUint8x16 ...) => (VPADDSB128 ...)", Message: "on unsigned 8-bit elements to VPADDSB, which takes signed 8-bit elements"},
			W{File: "simdAMD64.rules", Rule: "(AddSaturatedUint8x16 ...) => (VPADDUSB128 ...)"}},
		// VPMADDUBSW typed on 16-bit inputs.
		{"1be5eb2686",
			W{File: "simdAMD64.rules", Rule: "(SaturatedUnsignedSignedPairDotProdUint16x8 ...) => (VPMADDUBSW128 ...)", Message: "on unsigned 16-bit elements to VPMADDUBSW, which takes unsigned 8-bit elements"},
			W{File: "simdAMD64.rules", Rule: "(SaturatedUnsignedSignedPairDotProdUint8x16 ...) => (VPMADDUBSW128 ...)"}},
		// Alternating FMA lane parity swapped.
		{"fe0449ba3a",
			W{File: "simdAMD64.rules", Rule: "(MulAddEvenSubOddFloat32x4 ...) => (VFMADDSUB213PS128 ...)", Message: "needs add in even lanes, but VFMADDSUB213PS does sub in even lanes"},
			W{File: "simdAMD64.rules", Rule: "(MulAddEvenSubOddFloat32x4 ...) => (VFMSUBADD213PS128 ...)"}},
		// K-register op suffix taken from the element width.
		{"6565f5517e",
			W{File: "AMD64.rules", Rule: "(VPAND128 (VPMOVMToVec8x16 x) (VPMOVMToVec8x16 y)) && v.Block.CPUfeatures.hasFeature(CPUavx512) => (VPMOVMToVec8x16 (KANDB x y))", Message: "KANDB operates on 8 mask bits, but VPMOVMToVec8x16 has 16 lanes"},
			W{File: "AMD64.rules", Rule: "(VPAND128 (VPMOVMToVec8x16 x) (VPMOVMToVec8x16 y)) && v.Block.CPUfeatures.hasFeature(CPUavx512) => (VPMOVMToVec8x16 (KANDW x y))"}},
		// VPANDN to KANDN without swapping operands.
		{"e2889b0bf5",
			W{File: "AMD64.rules", Rule: "(VPANDN128 (VPMOVMToVec8x16 x) (VPMOVMToVec8x16 y)) && v.Block.CPUfeatures.HasFeature(ssa.CPUavx512) => (VPMOVMToVec8x16 (KANDNW x y))", Message: "and-not operands swapped: VPANDN128 complements x, but KANDNW"},
			W{File: "AMD64.rules", Rule: "(VPANDN128 (VPMOVMToVec8x16 x) (VPMOVMToVec8x16 y)) && v.Block.CPUfeatures.HasFeature(ssa.CPUavx512) => (VPMOVMToVec8x16 (KANDNW y x))"}},
	}
	for _, c := range cases {
		t.Run(c.rev, func(t *testing.T) {
			analysistest.RunRevision(t, c.rev+"^", simdnames.Analyzer, c.buggy)
			c.good.Absent = true
			analysistest.RunRevision(t, c.rev, simdnames.Analyzer, c.good)
		})
	}
}
