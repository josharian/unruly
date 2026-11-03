package divzero_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/divzero"
)

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, divzero.Analyzer)
}

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", divzero.Analyzer)
}

// go.dev/issue/43099: constant folds of integer division crashed the
// compiler on a constant zero divisor.
func TestConstantFold(t *testing.T) {
	analysistest.RunRevision(t, "6c64b6db68^", divzero.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(DIV   (MOVDconst [c]) (MOVDconst [d])) => (MOVDconst [c/d])", Message: `c / d in the result divides by zero if d is 0`},
		analysistest.Want{File: "ARM64.rules", Rule: "(UMODW (MOVDconst [c]) (MOVDconst [d])) => (MOVDconst [int64(uint32(c)%uint32(d))])", Message: `uint32\(c\) % uint32\(d\)`},
		analysistest.Want{File: "ARM.rules", Rule: "(Select0 (CALLudiv (MOVWconst [c]) (MOVWconst [d]))) =>", Message: `uint32\(c\) / uint32\(d\)`},
		analysistest.Want{File: "MIPS.rules", Rule: "(Select1 (DIV  (MOVWconst [c]) (MOVWconst [d]))) =>", Message: `c / d`},
		analysistest.Want{File: "MIPS64.rules", Rule: "(Select1 (DIVV  (MOVVconst [c]) (MOVVconst [d]))) =>", Message: `c / d`},
	)
	analysistest.RunRevision(t, "6c64b6db68", divzero.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(DIV   (MOVDconst [c]) (MOVDconst [d])) && d != 0 => (MOVDconst [c/d])", Absent: true},
		analysistest.Want{File: "ARM.rules", Rule: "(Select0 (CALLudiv (MOVWconst [c]) (MOVWconst [d]))) && d != 0 =>", Absent: true},
		analysistest.Want{File: "MIPS.rules", Rule: "(Select1 (DIV  (MOVWconst [c]) (MOVWconst [d]))) && d != 0 =>", Absent: true},
		analysistest.Want{File: "MIPS64.rules", Rule: "(Select1 (DIVV  (MOVVconst [c]) (MOVVconst [d]))) && d != 0 =>", Absent: true},
	)
}

// go.dev/issue/53018: the same, on LOONG64.
func TestConstantFoldLOONG64(t *testing.T) {
	analysistest.RunRevision(t, "a2bca290e7^", divzero.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "(Select1 (DIVV  (MOVVconst [c]) (MOVVconst [d]))) => (MOVVconst [c/d])", Message: `c / d in the result divides by zero if d is 0`},
		analysistest.Want{File: "LOONG64.rules", Rule: "(Select0 (DIVVU (MOVVconst [c]) (MOVVconst [d]))) => (MOVVconst [int64(uint64(c)%uint64(d))])", Message: `uint64\(c\) % uint64\(d\)`},
	)
	analysistest.RunRevision(t, "a2bca290e7", divzero.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "(Select1 (DIVV  (MOVVconst [c]) (MOVVconst [d]))) && d != 0 => (MOVVconst [c/d])", Absent: true},
	)
}
