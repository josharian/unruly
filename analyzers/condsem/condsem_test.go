package condsem_test

import (
	"path/filepath"
	"regexp"
	"testing"

	"github.com/josharian/unruly/analysis"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/condsem"
)

func Test(t *testing.T) {
	t.Parallel()
	analysistest.Run(t, "testdata", condsem.Analyzer)
}

func TestSurvey(t *testing.T) {
	t.Parallel()
	analysistest.Survey(t, condsem.Analyzer)
}

// Each historical test asserts the diagnostic at the buggy rule in the fix's
// parent and its absence (or the rule's deletion) in the fix.

func TestNoovInvertFlags(t *testing.T) {
	t.Parallel()
	// 607cfcea17: absorbing InvertFlags into a no-overflow comparison
	// swaps < and >, which is wrong when the subtraction overflows.
	analysistest.RunRevision(t, "607cfcea17^", condsem.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(LTnoov (InvertFlags cmp) yes no) => (GTnoov cmp yes no)", Message: `cmp = \(CMP`},
		analysistest.Want{File: "ARM64.rules", Rule: "(GEnoov (InvertFlags cmp) yes no) => (LEnoov cmp yes no)"},
		analysistest.Want{File: "ARM64.rules", Rule: "(LessThanNoov     (InvertFlags x))"},
		analysistest.Want{File: "ARM64.rules", Rule: "(GreaterEqualNoov (InvertFlags x))"},
		analysistest.Want{File: "ARM.rules", Rule: "(LTnoov (InvertFlags cmp) yes no) => (GTnoov cmp yes no)"},
		analysistest.Want{File: "ARM.rules", Rule: "(GTnoov (InvertFlags cmp) yes no) => (LTnoov cmp yes no)"},
	)
	// The fix deletes those rules; no inverted-CMP counterexample remains.
	diags := analysistest.RunRevision(t, "607cfcea17", condsem.Analyzer)
	absent(t, diags, "ARM64.rules", `(cmp|x) = \(CMP `)
	absent(t, diags, "ARM.rules", `(cmp|x) = \(CMP `)
}

func TestSETGFBlock(t *testing.T) {
	t.Parallel()
	// 38e988efb4: SETGF and SETGEF were mapped to UGE and UGT blocks.
	const rule = "(NE t:(TESTQ x:(MOVBQZX s:(SET(EQ|NE|L|G|LE|GE|A|B|AE|BE|EQF|NEF|GF|GEF) flags)) x) yes no)"
	analysistest.RunRevision(t, "38e988efb4^", condsem.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Message: `flags = \(UCOMISD`})
	analysistest.RunRevision(t, "38e988efb4", condsem.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Absent: true})
}

func TestTESTQToTESTL(t *testing.T) {
	t.Parallel()
	// 0e02baa59a: TESTL sets the sign flag from bit 31, TESTQ from bit 63.
	analysistest.RunRevision(t, "0e02baa59a^", condsem.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(TESTQ x y) && (zeroUpper32Bits(x, 3) || zeroUpper32Bits(y, 3)) => (TESTL x y)", Message: "condition LT"})
	// The fix deletes the rule.
	absent(t, analysistest.RunRevision(t, "0e02baa59a", condsem.Analyzer), "AMD64.rules", "TESTL")
}

// absent asserts that no diagnostic in file matches the regexp msg.
func absent(t *testing.T, diags []analysis.Diagnostic, file, msg string) {
	t.Helper()
	re := regexp.MustCompile(msg)
	for _, d := range diags {
		if filepath.Base(d.Pos.File) == file && re.MatchString(d.Message) {
			t.Errorf("unexpected diagnostic: %v", d)
		}
	}
}

func TestCMPWToTST(t *testing.T) {
	t.Parallel()
	// 91a2e921dd: CMPWconst [0] tests 32 bits, TSTconst 64.
	const rule = "(LessThan (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTconst [c] y))"
	analysistest.RunRevision(t, "91a2e921dd^", condsem.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: rule})
	analysistest.RunRevision(t, "91a2e921dd", condsem.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(LessThan (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTconst [c] y))", Absent: true})
}

func TestCMPNegToCMN(t *testing.T) {
	t.Parallel()
	// b7b44b3173: CMP x (NEG y) and CMN x y differ in V when y is the
	// minimum integer, so ordered comparisons differ.
	analysistest.RunRevision(t, "b7b44b3173^", condsem.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(LT (CMP x z:(NEG y)) yes no) && z.Uses == 1 => (LT (CMN x y) yes no)"},
		analysistest.Want{File: "ARM64.rules", Rule: "(EQ (CMP x z:(NEG y)) yes no) && z.Uses == 1 => (EQ (CMN x y) yes no)", Absent: true},
		analysistest.Want{File: "ARM.rules", Rule: "((LT|LE|EQ|NE|GE|GT) (CMP x (RSBconst [0] y))) => ((LT|LE|EQ|NE|GE|GT) (CMN x y))"},
	)
}

func TestARMTSTV(t *testing.T) {
	t.Parallel()
	// 4826abb6c2: ARM TST leaves V unchanged, so LT after it reads a stale V.
	analysistest.RunRevision(t, "4826abb6c2^", condsem.Analyzer,
		analysistest.Want{File: "ARM.rules", Rule: "(LT (CMPconst [0] l:(AND x y)) yes no) && l.Uses==1 => (LT (TST x y) yes no)", Message: "unchanged"},
		analysistest.Want{File: "ARM.rules", Rule: "(EQ (CMPconst [0] l:(AND x y)) yes no) && l.Uses==1 => (EQ (TST x y) yes no)", Absent: true},
	)
	analysistest.RunRevision(t, "4826abb6c2", condsem.Analyzer,
		analysistest.Want{File: "ARM.rules", Rule: "(LT (CMPconst [0] l:(AND x y)) yes no) && l.Uses==1 => (LTnoov (TST x y) yes no)", Absent: true},
	)
}

func TestPPC64CondSelect(t *testing.T) {
	t.Parallel()
	// 259735f97a: ISEL [2] selects its first arg on EQ, so testing
	// bool == 0 inverts CondSelect.
	analysistest.RunRevision(t, "259735f97a^", condsem.Analyzer,
		analysistest.Want{File: "PPC64.rules", Rule: "(CondSelect x y bool) && flagArg(bool) == nil => (ISEL [2] x y (CMPWconst [0] bool))"})
	analysistest.RunRevision(t, "259735f97a", condsem.Analyzer,
		analysistest.Want{File: "PPC64.rules", Rule: "(CondSelect x y bool) && flagArg(bool) == nil => (ISEL [6] x y (CMPWconst [0] bool))", Absent: true})
}
