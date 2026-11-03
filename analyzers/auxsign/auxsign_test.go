package auxsign_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/auxsign"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", auxsign.Analyzer)
}

// The rules that fold a load into a SIMD op with an unsigned imm8 passed
// it through int8, so an immediate >= 128 became negative in the
// ValAndOff, which the assembler rejects.
func TestSIMDImm8Load(t *testing.T) {
	const rule = "(VRNDSCALEPS128 [c] l:(VMOVDQUload128 {sym} [off] ptr mem))"
	analysistest.RunRevision(t, "3f6eabdf09^", auxsign.Analyzer,
		analysistest.Want{File: "simdAMD64.rules", Rule: rule, Message: `int32\(int8\(c\)\) moves VRNDSCALEPS128's zero-extended immediate c into VRNDSCALEPS128load, which sign-extends it`},
	)
	analysistest.RunRevision(t, "3f6eabdf09", auxsign.Analyzer,
		analysistest.Want{File: "simdAMD64.rules", Rule: rule, Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, auxsign.Analyzer)
}
