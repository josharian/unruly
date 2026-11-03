package memaddr_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/memaddr"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", memaddr.Analyzer)
}

// go.dev/issue/44823: store combining matched any offset and symbol on
// the inner stores.
func TestStoreCombineAux(t *testing.T) {
	analysistest.RunRevision(t, "a829114b21^", memaddr.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "x3:(MOVBstore p1 w mem)", Message: `x3 \(MOVBstore\) is combined with other memory ops but its \[offset\] and \{sym\} are unconstrained`},
		analysistest.Want{File: "S390X.rules", Rule: "x3:(MOVBstore p1 w mem)", Message: `x3 \(MOVBstore\) is combined`},
	)
	analysistest.RunRevision(t, "a829114b21", memaddr.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "x3:(MOVBstore [0] {s} p1 w mem)", Absent: true},
		analysistest.Want{File: "S390X.rules", Rule: "x3:(MOVBstore [0] {s} p1 w mem)", Absent: true},
	)
}

// go.dev/issue/49061: the combined MOVBE load used the higher of two
// sequential addresses.
func TestSequentialAddresses(t *testing.T) {
	analysistest.RunRevision(t, "b0351bfd7d^", memaddr.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(MOVBEQload [i] {s} p0 mem)", Message: `sequentialAddresses\(p1, p0, ...\) makes p0 the higher address`},
	)
	// b0351bfd7d reverted the rule; fe7df4c4d0 relanded it fixed.
	analysistest.RunRevision(t, "fe7df4c4d0", memaddr.Analyzer,
		analysistest.Want{File: "AMD64.rules", Rule: "(MOVBEQload [i] {s} p1 mem)", Absent: true},
	)
}

// go.dev/issue/43570: copy elimination read a volatile source after
// calls could clobber it.
func TestVolatileSource(t *testing.T) {
	analysistest.RunRevision(t, "304f769ffc^", memaddr.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "midmem:(Move {t2} [s] tmp2 src _))", Message: `!isVolatile\(src\)`},
		analysistest.Want{File: "generic.rules", Rule: "midmem:(VarDef (Move {t2} [s] tmp2 src _)))", Message: `!isVolatile\(src\)`},
	)
	analysistest.RunRevision(t, "304f769ffc", memaddr.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "midmem:(Move {t2} [s] tmp2 src _))", Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "midmem:(VarDef (Move {t2} [s] tmp2 src _)))", Absent: true},
	)
}

// CL 662935 (16a6b71f18) fixed nested store-to-load forwarding rules that
// compared the load's size with the outermost store's type instead of the
// forwarded one's, while relaxing t1.Compare(x.Type) == types.CMPeq to
// copyCompatibleType. Before it, the CMPeq conjunct already made the sizes
// equal, so the wrong comparison only lost optimizations and is not
// reported.
func TestForwardingSize(t *testing.T) {
	analysistest.RunRevision(t, "16a6b71f18^", memaddr.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 x _)))", Absent: true},
		analysistest.Want{File: "generic.rules", Rule: "(Load <t1> p1 (Store {t2} p2 _ (Store {t3} p3 _ (Store {t4} p4 x _))))", Absent: true},
	)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, memaddr.Analyzer)
}
