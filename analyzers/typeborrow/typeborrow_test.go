package typeborrow_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/typeborrow"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", typeborrow.Analyzer)
}

// RISCV64latelower's SLLI <t> [56]: fixed by 2952fe4f16.
func TestHistoricalRISCV64LateLowerSLLI(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		var ws []analysistest.Want
		for line := 6; line <= 14; line++ {
			ws = append(ws, analysistest.Want{File: "RISCV64latelower.rules", Line: line, Message: `^\(SLLI <t> \[(56|48|32)\] \.\.\.\) has only zeros`, Absent: absent})
		}
		return ws
	}
	analysistest.RunRevision(t, "2952fe4f16^", typeborrow.Analyzer, want(false)...)
	analysistest.RunRevision(t, "2952fe4f16", typeborrow.Analyzer, want(true)...)
}

// Byteswapped stores typed <w.Type>: fixed by b3bc8620f8.
func TestHistoricalByteswapStore(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		ws := []analysistest.Want{
			{File: "AMD64.rules", Rule: "(MOVWstore [i-1] {s} p (ROLWconst", Message: `MOVWstore stores 2 bytes of \(ROLWconst`},
			{File: "AMD64.rules", Rule: "(MOVLstore [i-3] {s} p (BSWAPL", Message: `MOVLstore stores 4 bytes of \(BSWAPL`},
			{File: "AMD64.rules", Rule: "(MOVQstore [i-7] {s} p (BSWAPQ", Message: `MOVQstore stores 8 bytes of \(BSWAPQ`},
			{File: "ARM64.rules", Rule: "(MOVDstore [i-7] {s} ptr (REV", Message: `MOVDstore stores 8 bytes of \(REV`},
			{File: "ARM64.rules", Rule: "(MOVDstoreidx ptr0 idx0 (REV", Message: `MOVDstoreidx stores 8 bytes of \(REV`},
		}
		for i := range ws {
			ws[i].Absent = absent
		}
		return ws
	}
	analysistest.RunRevision(t, "b3bc8620f8^", typeborrow.Analyzer, want(false)...)
	analysistest.RunRevision(t, "b3bc8620f8", typeborrow.Analyzer, want(true)...)
}

// splitload's untyped pointer-width loads: fixed by 80123ef4bf.
func TestHistoricalSplitload(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		ws := []analysistest.Want{
			{File: "AMD64splitload.rules", Rule: "(CMP(Q|L|W|B)load {sym} [off] ptr x mem)", Message: `\(MOVQload \.\.\.\) compared with x`},
			{File: "AMD64splitload.rules", Rule: "(CMP(Q|L|W|B)loadidx1 {sym}", Message: `\(MOVQloadidx1 \.\.\.\) compared with x`},
			{File: "AMD64splitload.rules", Rule: "(CMPQloadidx8 {sym}", Message: `\(MOVQloadidx8 \.\.\.\) compared with x`},
			{File: "386splitload.rules", Rule: "(CMP(L|W|B)load {sym} [off] ptr x mem)", Message: `\(MOVLload \.\.\.\) compared with x`},
		}
		for i := range ws {
			ws[i].Absent = absent
		}
		return ws
	}
	analysistest.RunRevision(t, "80123ef4bf^", typeborrow.Analyzer, want(false)...)
	analysistest.RunRevision(t, "80123ef4bf", typeborrow.Analyzer, want(true)...)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, typeborrow.Analyzer)
}
