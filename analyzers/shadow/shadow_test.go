package shadow_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/shadow"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", shadow.Analyzer)
}

// The first typed rules.
func TestFirstTyped(t *testing.T) {
	analysistest.RunRevision(t, "79a3482d9e", shadow.Analyzer,
		analysistest.Want{File: "PPC64.rules", Line: 557, Message: `never fires: PPC64.rules:462`},
		analysistest.Want{File: "PPC64.rules", Line: 462, Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "(Sub(64|32|16|8) (Add(64|32|16|8) x y) y) => x", Message: "never fires"},
	)
}

// CL 420434 added rules folding signed compares of a 64-bit AND into TST,
// but wrote CMPWconst, so an earlier TSTWconst rule shadowed them (and
// had they fired, they would have tested 64 bits of a 32-bit compare).
func TestARM64TST(t *testing.T) {
	for _, op := range []string{"LessThan", "LessEqual", "GreaterThan", "GreaterEqual"} {
		analysistest.RunRevision(t, "91a2e921dd^", shadow.Analyzer,
			analysistest.Want{File: "ARM64.rules", Rule: "(" + op + " (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (" + op + " (TSTconst", Message: "never fires: ARM64.rules:"},
		)
		analysistest.RunRevision(t, "91a2e921dd", shadow.Analyzer,
			analysistest.Want{File: "ARM64.rules", Rule: "(" + op + " (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (" + op + " (TSTconst", Absent: true},
		)
	}
}

// PPC64.rules had both ((EQ|NE) (CMPconst [0] (Select0 (ANDCCconst ...))))
// and ((EQ|NE|LT|LE|GT|GE) ...) versions of the same rule.
func TestPPC64ANDCC(t *testing.T) {
	analysistest.RunRevision(t, "80834af206^", shadow.Analyzer,
		analysistest.Want{File: "PPC64.rules", Line: 410, Message: `expansion \(EQ \(CMPconst .* never fires: PPC64.rules:327`},
		analysistest.Want{File: "PPC64.rules", Line: 411, Message: `expansion \(NE \(CMPWconst .* never fires: PPC64.rules:328`},
	)
	analysistest.RunRevision(t, "80834af206", shadow.Analyzer,
		analysistest.Want{File: "PPC64.rules", Rule: "((EQ|NE|LT|LE|GT|GE) (CMPconst [0] (Select0 z:(ANDCCconst [c] x))) yes no)", Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, shadow.Analyzer)
}
