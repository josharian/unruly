package selfrewrite_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/selfrewrite"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", selfrewrite.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, selfrewrite.Analyzer)
}
