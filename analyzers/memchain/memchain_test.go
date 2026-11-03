package memchain_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/memchain"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", memchain.Analyzer)
}

// go.dev/issue/58161: the memory half of make([]T, 0) elimination
// bypassed the call while its pointer result kept it live.
func TestMakesliceBypass(t *testing.T) {
	analysistest.RunRevision(t, "0d8d181bd5^", memchain.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(SelectN [1] call:(StaticLECall _ (Const(64|32) [0]) (Const(64|32) [0]) mem))", Message: `result skips call \(StaticLECall\).*call\.Uses == 1`},
	)
	analysistest.RunRevision(t, "0d8d181bd5", memchain.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(StaticLECall {callAux} _ (Const(64|32) [0]) (Const(64|32) [0]) mem)", Absent: true},
	)
}

// go.dev/issue/59973 (the BSWAP(MOVBE) half): BSWAP of a MOVBE load
// re-issued the load without checking that the MOVBE load died.
func TestBswapMOVBEReissue(t *testing.T) {
	analysistest.RunRevision(t, "10141676d1^", memchain.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(BSWAP(Q|L) (MOVBE(Q|L)load [i] {s} p m))", Message: `load MOVBE(Q|L)load is re-issued as MOV(Q|L)load`},
	)
	analysistest.RunRevision(t, "10141676d1", memchain.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(BSWAP(Q|L) x:(MOVBE(Q|L)load [i] {s} p mem))", Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, memchain.Analyzer)
}
