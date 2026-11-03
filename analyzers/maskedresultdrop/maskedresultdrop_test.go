package maskedresultdrop_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/maskedresultdrop"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", maskedresultdrop.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, maskedresultdrop.Analyzer)
}

// TestTip pins findings on the Go tree at aa94415944 (October 2026).
func TestTip(t *testing.T) {
	analysistest.RunRevision(t, "aa94415944", maskedresultdrop.Analyzer,
		analysistest.Want{File: "simdAMD64.rules", Rule: "(VPSLLWMasked512const [a] x mask) && a==0 => x", Message: "mask dropped: VPSLLWMasked512const zeroes the lanes where mask is false"},
		analysistest.Want{File: "simdAMD64.rules", Rule: "(VPSLLW512const [a] x) && a==0 => x", Absent: true},
	)
}
