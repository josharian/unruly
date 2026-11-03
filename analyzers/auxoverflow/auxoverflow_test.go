package auxoverflow_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/auxoverflow"
)

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, auxoverflow.Analyzer)
}

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", auxoverflow.Analyzer)
}

// go.dev/issue/81240, go.dev/issue/81242: RISCV64 packed Move and Zero
// sizes into a ValAndOff with int32(s), truncating sizes of 2 GB and up.
// The unrolled forms are bounded by 24*MoveSize, at most 192 bytes.
func TestRISCV64LoopSize(t *testing.T) {
	analysistest.RunRevision(t, "5c1ad454f5^", auxoverflow.Analyzer,
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredZeroLoop [ssa.MakeValAndOff(int32(s),int32(t.Alignment()))] ptr mem)", Message: `int32\(s\) truncates in int32: .*; LoweredZeroLoop's value is a size`},
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredMoveLoop [ssa.MakeValAndOff(int32(s),int32(t.Alignment()))] dst src mem)", Message: `int32\(s\) truncates in int32: .*; LoweredMoveLoop's value is a size`},
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredZero [ssa.MakeValAndOff(int32(s),int32(t.Alignment()))] ptr mem)", Absent: true},
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredMove [ssa.MakeValAndOff(int32(s),int32(t.Alignment()))] dst src mem)", Absent: true},
	)
	analysistest.RunRevision(t, "5c1ad454f5", auxoverflow.Analyzer,
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredZeroLoop [s] {t.Alignment()} ptr mem)", Absent: true},
		analysistest.Want{File: "RISCV64.rules", Rule: "(LoweredMoveLoop [s] {t.Alignment()} dst src mem)", Absent: true},
	)
}

// go.dev/issue/80613: MIPS64 lowered any OffPtr to ADDVconst, whose
// immediate the assembler truncates to 32 bits.
func TestMIPS64OffPtr(t *testing.T) {
	analysistest.RunRevision(t, "d52464487f^", auxoverflow.Analyzer,
		analysistest.Want{File: "MIPS64.rules", Rule: "(OffPtr [off] ptr) => (ADDVconst [off] ptr)", Message: `off may be 2147483648, which does not fit in int32`},
	)
	analysistest.RunRevision(t, "d52464487f", auxoverflow.Analyzer,
		analysistest.Want{File: "MIPS64.rules", Rule: "(OffPtr [off] ptr) &&  is32Bit(off) => (ADDVconst [off] ptr)", Absent: true},
	)
}

// AMD64 SIMD shifts by a constant truncated the 64-bit count with
// uint8(c), so a shift by 256 became a shift by 0.
func TestSIMDShiftCount(t *testing.T) {
	analysistest.RunRevision(t, "39b20d32a9^", auxoverflow.Analyzer,
		analysistest.Want{File: "simdAMD64.rules", Rule: "(VPSLLW128 x (MOVQconst [c])) => (VPSLLW128const [uint8(c)] x)", Message: `uint8\(c\) truncates in uint8: its value may be 256, which becomes 0`},
		analysistest.Want{File: "simdAMD64.rules", Rule: "(VPSRAQ512 x (MOVQconst [c])) => (VPSRAQ512const [uint8(c)] x)", Message: `uint8\(c\) truncates`},
	)
	analysistest.RunRevision(t, "39b20d32a9", auxoverflow.Analyzer,
		analysistest.Want{File: "simdAMD64.rules", Rule: "(VPSLLW128 x (MOVQconst [c])) => (VPSLLW128const [amd64CapAVXShift(c)] x)", Absent: true},
	)
}
