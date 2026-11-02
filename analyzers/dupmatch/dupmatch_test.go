package dupmatch_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/dupmatch"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", dupmatch.Analyzer)
}

func TestHistorical(t *testing.T) {
	analysistest.RunRevision(t, "79a3482d9e", dupmatch.Analyzer,
		analysistest.Want{File: "PPC64.rules", Line: 557, Message: `shadowed by equivalent rule at PPC64.rules:462`},
		analysistest.Want{File: "PPC64.rules", Line: 462, Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "(Sub(64|32|16|8) (Add(64|32|16|8) x y) y) => x", Message: "shadowed"},
	)
}
