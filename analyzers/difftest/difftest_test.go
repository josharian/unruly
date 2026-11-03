package difftest

import (
	"fmt"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/rules"
)

// Test checks the fixtures' diagnostics, and that difftest evaluated
// every fixture rule, so that a correct fixture can't pass vacuously.
func Test(t *testing.T) {
	var unexercised []string
	trace = func(r *rules.Rule, sat int, stop error) {
		switch {
		case stop != nil:
			unexercised = append(unexercised, fmt.Sprintf("%s: %v", r.Pos, stop))
		case sat == 0:
			unexercised = append(unexercised, fmt.Sprintf("%s: no generated input matched", r.Pos))
		}
	}
	defer func() { trace = nil }()
	analysistest.Run(t, "testdata", Analyzer)
	for _, u := range unexercised {
		t.Errorf("fixture rule not exercised: %s", u)
	}
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, Analyzer)
}

// 9b8742f2e7 guarded the float-to-int constant folds: converting an
// out-of-range float in the compiler gives a result that depends on the
// machine the compiler runs on.
func TestHostDependentConversion(t *testing.T) {
	const rule = "(Cvt64Fto64 (Const64F [c]))"
	analysistest.RunRevision(t, "9b8742f2e7^", Analyzer,
		analysistest.Want{File: "generic.rules", Rule: rule + " => (Const64 [int64(c)])", Message: `host-dependent: converting .* to int64`},
		analysistest.Want{File: "generic.rules", Rule: "(Cvt32Fto32 (Const32F [c])) => (Const32 [int32(c)])", Message: `host-dependent: converting .* to int32`},
	)
	analysistest.RunRevision(t, "9b8742f2e7", Analyzer,
		analysistest.Want{File: "generic.rules", Rule: rule + " && c >= -1<<63", Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "(Cvt32Fto32 (Const32F [c])) && c >= -1<<31", Absent: true},
	)
}
