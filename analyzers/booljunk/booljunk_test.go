package booljunk_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/booljunk"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", booljunk.Analyzer)
}

// TestHistorical checks the fixes of bool-junk bugs. (b3b442449b, which
// fixed loong64's If lowering, landed just before e5615ad876 enabled
// loong64's register ABI, so its parent has no junk bools to find; the
// LOONG64 fixture covers it.)
func TestHistorical(t *testing.T) {
	for _, tt := range []struct {
		rev, file, rule, msg string
	}{
		{"e8f78cb60c", "ARM64.rules", "(CondSelect x y boolval) && flagArg(boolval) == nil", "CMPWconst reads the whole register of boolval"},
		{"888047c310", "PPC64.rules", "(CondSelect x y bool) && flagArg(bool) == nil", "CMPWconst reads the whole register of bool"},
		{"7a574ff23f", "PPC64.rules", "(If cond yes no) =>", "CMPWconst reads the whole register of cond"},
		{"9ae7dc3040", "ARM64.rules", "(If cond yes no) =>", "NZ branches on the whole register of cond"},
		{"d6e6140c98", "RISCV64.rules", "(If cond yes no) =>", "BNEZ branches on the whole register of cond"},
	} {
		t.Run(tt.rev, func(t *testing.T) {
			analysistest.RunRevision(t, tt.rev+"^", booljunk.Analyzer,
				analysistest.Want{File: tt.file, Rule: tt.rule, Message: tt.msg})
			analysistest.RunRevision(t, tt.rev, booljunk.Analyzer,
				analysistest.Want{File: tt.file, Rule: tt.rule, Absent: true})
		})
	}
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, booljunk.Analyzer)
}
