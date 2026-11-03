package valuekind_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/valuekind"
)

func Test(t *testing.T) { analysistest.Run(t, "testdata", valuekind.Analyzer) }

// The fixtures also cover 398a8ed653, 23f3ea82b9, and 624630b824, whose
// rules predate typed rules and so can't be loaded.

func TestHistoricalAtomicAnd(t *testing.T) {
	// Generic AtomicAnd8 was a (Uint8, Mem) tuple, which AMD64 and
	// S390X lowered to memory-only ops; dbfa3cacc7 split it into a
	// memory op and a tuple-valued AtomicAnd8value.
	const rule = "(AtomicAnd8 ptr val mem) => (ANDBlock ptr val mem)"
	analysistest.RunRevision(t, "dbfa3cacc7^", valuekind.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Message: "AtomicAnd8 is a tuple, but ANDBlock produces memory"},
		analysistest.Want{File: "S390X.rules", Rule: "(AtomicAnd32 ...) => (LAN ...)", Message: "produces memory"},
	)
	analysistest.RunRevision(t, "dbfa3cacc7", valuekind.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: rule, Absent: true},
		analysistest.Want{File: "S390X.rules", Rule: "(AtomicAnd32 ...) => (LAN ...)", Absent: true},
	)
}

func TestHistoricalLoong64Cvt(t *testing.T) {
	// go.dev/issue/81000: TRUNCDW leaves Cvt64Fto32's integer result
	// in an FP register.
	analysistest.RunRevision(t, "849501bbd9^", valuekind.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "(Cvt64Fto32 ...) => (TRUNCDW ...)", Message: "TRUNCDW writes a floating-point register"},
		analysistest.Want{File: "LOONG64.rules", Rule: "(Cvt32Fto64 ...) => (TRUNCFV ...)", Message: "TRUNCFV writes a floating-point register"},
	)
	analysistest.RunRevision(t, "849501bbd9", valuekind.Analyzer,
		analysistest.Want{File: "LOONG64.rules", Rule: "(Cvt64Fto32 <t> x) => (MOVWfpgp (TRUNCDW <t> x))", Absent: true},
		analysistest.Want{File: "LOONG64.rules", Rule: "(Cvt32Fto64 <t> x) => (MOVVfpgp (TRUNCFV <t> x))", Absent: true},
	)
}

func TestSurvey(t *testing.T) { analysistest.Survey(t, valuekind.Analyzer) }
