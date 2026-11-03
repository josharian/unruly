package placement_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/placement"
)

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, placement.Analyzer)
}

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", placement.Analyzer)
}

// Rules before 79a3482d9e (October 2020) are untyped and don't load, so
// these fixes have no historical test, only fixtures in testdata:
// 334d410ae3 (S390X Select1 placement, in a rule set where selectors are
// now moved by the tighten tuple selectors pass), cde977c23c and
// 41f9f6f471 (merged loads in the wrong block), b81f2f106f (combined
// load hoisted to the first load's block), 769fda2d51 (mergePoint
// missing an operand), and fbfbf03b28 (@mem.Block using an outside
// pointer).

func TestCmpstringSelector(t *testing.T) {
	analysistest.RunRevision(t, "9f9dd2bfd8^", placement.Analyzer,
		analysistest.Want{File: "generic.rules", Line: 2802, Message: `SelectN of c is created in v.Block, but a tuple selector must be in its tuple's block`},
	)
	analysistest.RunRevision(t, "9f9dd2bfd8", placement.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [0] (StaticLECall {f} x y (SelectN [1] c:(StaticLECall {g} x y mem))))", Absent: true},
	)
}

func TestBswapLoad(t *testing.T) {
	analysistest.RunRevision(t, "10141676d1^", placement.Analyzer,
		analysistest.Want{File: "AMD64.rules", Line: 1722, Message: `AMD64MOVBEQload is created in v.Block with memory arg mem from x \(AMD64MOVQload\)`},
		analysistest.Want{File: "AMD64.rules", Line: 1723, Message: `AMD64MOVQload is created in v.Block with memory arg m from AMD64MOVBEQload`},
	)
	analysistest.RunRevision(t, "10141676d1", placement.Analyzer,
		analysistest.Want{File: "AMD64.rules", Line: 1723, Absent: true},
		analysistest.Want{File: "AMD64.rules", Line: 1724, Absent: true},
	)
}

func TestPhiInBlockRule(t *testing.T) {
	analysistest.RunRevision(t, "8893da7c72^", placement.Analyzer,
		analysistest.Want{File: "generic.rules", Line: 964, Message: `Phi is created in the If block by a block rule`},
	)
	analysistest.RunRevision(t, "8893da7c72", placement.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(Phi <t> nx:(Not x) ny:(Not y))", Absent: true},
	)
}
