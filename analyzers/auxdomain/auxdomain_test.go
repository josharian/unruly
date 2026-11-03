package auxdomain_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/auxdomain"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", auxdomain.Analyzer)
}

// (SHL(Q|L)const [c] (ADD(Q|L) x x)) => (SHL(Q|L)const [c+1] x) turned
// (x+x)<<63, which is 0, into SHLQconst [64], a shift by 0.
func TestAMD64ShiftDouble(t *testing.T) {
	analysistest.RunRevision(t, "c3bfc824a5^", auxdomain.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(SHL(Q|L)const [c] (ADD(Q|L) x x))", Message: `SHLQconst \[c \+ 1\] is 64, outside \[0, 63\].*when c=63`},
		analysistest.Want{File: "AMD64.rules", Rule: "(SHL(Q|L)const [c] (ADD(Q|L) x x))", Message: `SHLLconst \[c \+ 1\] is 32, outside \[0, 31\].*when c=31`},
	)
	analysistest.RunRevision(t, "c3bfc824a5", auxdomain.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(SHLQconst [c] (ADDQ x x)) && c < 63", Absent: true},
		analysistest.Want{File: "AMD64.rules", Rule: "(SHLLconst [c] (ADDL x x)) && c < 31", Absent: true},
	)
}

// The same bug on loong64 (issue 75479).
func TestLOONG64ShiftDouble(t *testing.T) {
	analysistest.RunRevision(t, "78ef487a6f^", auxdomain.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "((SLLV|SLL)const [c] (ADDV x x))", Message: `SLLconst \[c \+ 1\] is 32, outside \[0, 31\].*when c=31`},
	)
	analysistest.RunRevision(t, "78ef487a6f", auxdomain.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "((SLLV|SLL)const <t> [c] (ADDV x x)) && c < t.Size() * 8 - 1", Absent: true},
	)
}

// (SRLI <t> [x] (MOVWUreg y)) => (SRLIW <t> [int64(x&31)] y) turned
// uint64(uint32(v)) >> 40, which is 0, into a shift by 8.
func TestRISCV64MaskedCount(t *testing.T) {
	analysistest.RunRevision(t, "70c7fb75e9^", auxdomain.Analyzer,
		analysistest.Want{File: "RISCV64.rules", Rule: "(SRLI <t> [x] (MOVWUreg y)) => (SRLIW <t> [int64(x&31)] y)", Message: `masks SRLI's count x, which is in \[0, 63\]`},
		analysistest.Want{File: "RISCV64.rules", Rule: "(SRAI <t> [x] (MOVWreg y)) => (SRAIW <t> [int64(x&31)] y)", Message: `masks SRAI's count x`},
	)
	analysistest.RunRevision(t, "70c7fb75e9", auxdomain.Analyzer,
		analysistest.Want{File: "RISCV64.rules", Rule: "(SRLI <t> [x] (MOVWUreg y)) && x >= 0 && x <= 31", Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, auxdomain.Analyzer)
}
