package loweringcoverage_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/loweringcoverage"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", loweringcoverage.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, loweringcoverage.Analyzer)
}

// PPC64 lowered 8-byte stores only for int and pointer values, so a store
// of struct{ m map[int]int } matched no rule (issue 45344).
func TestRevision94323206ae(t *testing.T) {
	analysistest.RunRevision(t, "94323206ae^", loweringcoverage.Analyzer,
		analysistest.Want{File: "PPC64.rules", Line: 580, Message: `\(Store \{t\} ptr val mem\): t=struct\{ p \*T \}`})
	analysistest.RunRevision(t, "94323206ae", loweringcoverage.Analyzer,
		analysistest.Want{File: "PPC64.rules", Line: 580, Absent: true})
}

// ARM64 lowered Load and Store of 8-byte SVE predicates but not
// ZeroSIMD (issue 81080).
func TestRevision276175b8fe(t *testing.T) {
	analysistest.RunRevision(t, "276175b8fe^", loweringcoverage.Analyzer,
		analysistest.Want{File: "ARM64.rules", Line: 1883, Message: `\(ZeroSIMD <t>\): 8-byte SIMD type`})
	analysistest.RunRevision(t, "276175b8fe", loweringcoverage.Analyzer,
		analysistest.Want{File: "ARM64.rules", Line: 1883, Absent: true})
}

// OffPtr of SP lowered to a plain add on 386, PPC64, and Wasm, which is
// not rematerializeable (issue 42944).
func TestRevision37a32a1833(t *testing.T) {
	analysistest.RunRevision(t, "37a32a1833^", loweringcoverage.Analyzer,
		analysistest.Want{File: "386.rules", Line: 52, Message: `\(OffPtr \[8\] \(SP\)\) lowers to \(ADDLconst \[8\] \(SP\)\), which is not rematerializeable`},
		analysistest.Want{File: "PPC64.rules", Line: 347, Message: `lowers to \(ADDconst \[8\] \(SP\)\), which is not rematerializeable`},
		analysistest.Want{File: "Wasm.rules", Line: 48, Message: `lowers to \(I64AddConst \[8\] \(SP\)\), which is not rematerializeable`})
	analysistest.RunRevision(t, "37a32a1833", loweringcoverage.Analyzer,
		analysistest.Want{File: "386.rules", Line: 52, Absent: true},
		analysistest.Want{File: "PPC64.rules", Line: 347, Absent: true},
		analysistest.Want{File: "Wasm.rules", Line: 48, Absent: true})
}
