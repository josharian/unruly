package simdmaskshape_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/simdmaskshape"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", simdmaskshape.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, simdmaskshape.Analyzer)
}

// TestTip pins findings on the Go tree at aa94415944 (October 2026).
func TestTip(t *testing.T) {
	const f = "simdAMD64.rules"
	analysistest.RunRevision(t, "aa94415944", simdmaskshape.Analyzer,
		// Natural code: x.DotProductPairs(y).IfElse(m, z).
		analysistest.Want{File: f, Line: 2236, Message: `VPMADDWD writes 32-bit elements .* from VPMOVVec16x8ToM.* by m\[0 0 1 1\] instead of m\[0 1 2 3\]`},
		// Natural code: x.TruncToInt8().IfElse(m, z).
		analysistest.Want{File: f, Line: 2253, Message: `merge coverage: VPMOVDB writes only 4 of its 16 result elements`},
		// Reinterpretation: x.Add(y).AsInt8x16().IfElse(m, z).
		analysistest.Want{File: f, Line: 2212, Message: `VPBLENDVB selects bytes, but VPMOVVec32x4ToM keeps only the top bit`},
		// Reinterpretation: x.SaturateToInt16().AsInt32x4().Masked(m).
		analysistest.Want{File: f, Line: 1812, Message: `VMOVDQU32Masked128 selects 32-bit lanes, but VPMOVSDW writes 16-bit elements`},
		analysistest.Want{File: f, Line: 2055, Message: `VPBLENDMDMasked512 selects 32-bit lanes, but VPACKSSDW writes 16-bit elements`},
		analysistest.Want{File: f, Line: 2181, Message: `never matches: VPBLENDVB128 operates on Vec128 but VCVTPS2PD256 produces Vec256`},
		// Sound fusions.
		analysistest.Want{File: f, Line: 1477, Absent: true},
		analysistest.Want{File: f, Line: 2057, Absent: true},
		analysistest.Want{File: f, Line: 2205, Absent: true},
	)
}
