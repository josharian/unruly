package argtype_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/argtype"
)

func Test(t *testing.T) { analysistest.Run(t, "testdata", argtype.Analyzer) }

// The fixtures also cover d4cc51d411, d585f04fd3, and 8f854244ad,
// whose rules predate typed rules and so can't be loaded.

func TestHistoricalStoreType(t *testing.T) {
	// 60140a86b3 made every Store lowering use {t} instead of val.Type.
	analysistest.RunRevision(t, "60140a86b3^", argtype.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(Store {t} ptr val mem) && t.Size() == 8 && is64BitFloat(val.Type) => (MOVSDstore ptr val mem)", Message: `condition reads val.Type`},
		analysistest.Want{File: "RISCV64.rules", Rule: "(Store {t} ptr val mem) && t.Size() == 8 && !is64BitFloat(val.Type) => (MOVDstore ptr val mem)", Message: `condition reads val.Type`},
	)
	analysistest.RunRevision(t, "60140a86b3", argtype.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(Store {t} ptr val mem) && t.Size() == 8 && t.IsFloat() => (MOVSDstore ptr val mem)", Absent: true},
		analysistest.Want{File: "RISCV64.rules", Rule: "(Store {t} ptr val mem) && t.Size() == 8 && !t.IsFloat() => (MOVDstore ptr val mem)", Absent: true},
	)
}

func TestHistoricalPPC64Store(t *testing.T) {
	// A pointer-shaped struct value is neither is64BitInt nor isPtr, so
	// no PPC64 Store rule matched it (go.dev/issue/45344). 94323206ae
	// changed the test to !is64BitFloat(val.Type), still reading val's
	// type; 60140a86b3 (above) removed that.
	analysistest.RunRevision(t, "94323206ae^", argtype.Analyzer,
		analysistest.Want{File: "PPC64.rules", Rule: "(is64BitInt(val.Type) || isPtr(val.Type))", Message: `condition reads val.Type`},
	)
}

func TestHistoricalMemmove(t *testing.T) {
	// go.dev/issue/55122: the Move's type came from dst's type, which
	// CSE and pointer conversions make unreliable.
	analysistest.RunRevision(t, "e283473ebb^", argtype.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [0] call:(StaticLECall {sym} dst src (Const(64|32) [sz]) mem))", Message: `dst\.Type\.Elem\(\)`},
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [0] call:(StaticCall {sym} dst src (Const(64|32) [sz]) mem))", Message: `dst\.Type\.Elem\(\)`},
		analysistest.Want{File: "generic.rules", Rule: "s3:(Store {t} _ dst mem)))))", Message: `t\.Elem\(\) on the {t} of a Store`},
	)
	analysistest.RunRevision(t, "e283473ebb", argtype.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [0] call:(StaticLECall {sym} dst src (Const(64|32) [sz]) mem))", Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [0] call:(StaticCall {sym} dst src (Const(64|32) [sz]) mem))", Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "s3:(Store {t} _ dst mem)))))", Absent: true},
	)
}

func TestHistoricalDirectIface(t *testing.T) {
	// go.dev/issue/63505.
	analysistest.RunRevision(t, "eb832afb23^", argtype.Analyzer,
		analysistest.Want{File: "dec.rules", Rule: "(StructMake1 x) && x.Type.IsPtr() => x", Message: `IsPtrShaped`},
		analysistest.Want{File: "dec.rules", Rule: "(ArraySelect [0] x) && x.Type.IsPtr() => x", Message: `IsPtrShaped`},
	)
	analysistest.RunRevision(t, "eb832afb23", argtype.Analyzer,
		analysistest.Want{File: "dec.rules", Rule: "(StructMake1 x) && x.Type.IsPtrShaped() => x", Absent: true},
		analysistest.Want{File: "dec.rules", Rule: "(ArraySelect [0] x) && x.Type.IsPtrShaped() => x", Absent: true},
	)
}

func TestSurvey(t *testing.T) { analysistest.Survey(t, argtype.Analyzer) }
