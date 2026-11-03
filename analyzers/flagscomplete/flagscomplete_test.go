package flagscomplete_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/flagscomplete"
)

func Test(t *testing.T) {
	t.Parallel()
	analysistest.Run(t, "testdata", flagscomplete.Analyzer)
}

func TestSurvey(t *testing.T) {
	t.Parallel()
	analysistest.Survey(t, flagscomplete.Analyzer)
}

func TestADCQInvertFlags(t *testing.T) {
	t.Parallel()
	// 9f9476d09b: ADCQ and SBBQ had no InvertFlags absorption, but
	// (Select1 (NEGLflags (MOVBQZX (SETB x)))) => x hands them SETB's flags.
	const rule = "(Select0 (Add64carry x y c)) => (Select0 (ADCQ x y (Select1 <types.TypeFlags> (NEGLflags c))))"
	analysistest.RunRevision(t, "9f9476d09b^", flagscomplete.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Message: "ADCQ's flags may be InvertFlags"})
	analysistest.RunRevision(t, "9f9476d09b", flagscomplete.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Message: "InvertFlags", Absent: true})
}

func TestNoovInvertFlags(t *testing.T) {
	t.Parallel()
	// fb5bdb4cc9: LessThanNoov of a CMP, which can become InvertFlags.
	const rule = "((Equal|NotEqual|LessThan|GreaterEqual) (CMPconst  [0] z:(MSUB     a x y)))"
	analysistest.RunRevision(t, "fb5bdb4cc9^", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: rule, Message: "LessThanNoov's flags may be InvertFlags"})
	analysistest.RunRevision(t, "fb5bdb4cc9", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: rule, Message: "InvertFlags", Absent: true})
}

func TestNoovFlagConstant(t *testing.T) {
	t.Parallel()
	// af278bfb1f: LessThanNoov of a CMNconst, which can fold to FlagConstant.
	const rule = "((Equal|NotEqual|LessThan|GreaterEqual) (CMPconst  [0] x:(ADDconst [c] y))) && x.Uses == 1"
	analysistest.RunRevision(t, "af278bfb1f^", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: rule, Message: "LessThanNoov's flags may be FlagConstant"})
	analysistest.RunRevision(t, "af278bfb1f", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: rule, Absent: true})
}

func TestConditionalFlagConstant(t *testing.T) {
	t.Parallel()
	// 8d77e45064: CSETM, CSINC, CSINV, and CSNEG took CSEL's flags, which
	// may be constant, without rules to fold them.
	analysistest.RunRevision(t, "8d77e45064^", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(CSEL [cc] (MOVDconst [-1]) (MOVDconst [0]) flag) => (CSETM [cc] flag)", Message: "CSETM's flags may be FlagConstant"},
		analysistest.Want{File: "ARM64.rules", Rule: "(CSEL [cc] x (ADDconst [1] a) flag) => (CSINC [cc] x a flag)", Message: "CSINC"},
		analysistest.Want{File: "ARM64.rules", Rule: "(CSEL [cc] x (MVN a) flag) => (CSINV [cc] x a flag)", Message: "CSINV"},
		analysistest.Want{File: "ARM64.rules", Rule: "(CSEL [cc] x (NEG a) flag) => (CSNEG [cc] x a flag)", Message: "CSNEG"},
	)
	analysistest.RunRevision(t, "8d77e45064", flagscomplete.Analyzer,
		analysistest.Want{File: "ARM64.rules", Rule: "(CSEL [cc] x (NEG a) flag) => (CSNEG [cc] x a flag)", Absent: true})
}
