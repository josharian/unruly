package rewritecycle_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/rewritecycle"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", rewritecycle.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, rewritecycle.Analyzer)
}
