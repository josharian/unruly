package nanconst_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/nanconst"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", nanconst.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, nanconst.Analyzer)
}

func TestHistorical(t *testing.T) {
	// Constant folds of float-to-int conversions depended on the host's
	// handling of out-of-range values. Leave them for run time.
	cvt := []string{
		"(Cvt32Fto32 (Const32F [c]))",
		"(Cvt32Fto64 (Const32F [c]))",
		"(Cvt64Fto32 (Const64F [c]))",
		"(Cvt64Fto64 (Const64F [c]))",
	}
	var before, after []analysistest.Want
	for _, r := range cvt {
		before = append(before, analysistest.Want{File: "generic.rules", Rule: r, Message: `is implementation-defined`})
		after = append(after, analysistest.Want{File: "generic.rules", Rule: r, Absent: true})
	}
	analysistest.RunRevision(t, "9b8742f2e7^", nanconst.Analyzer, before...)
	analysistest.RunRevision(t, "9b8742f2e7", nanconst.Analyzer, after...)
}
