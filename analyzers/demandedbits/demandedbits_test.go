package demandedbits_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/demandedbits"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", demandedbits.Analyzer)
}

func TestHistorical(t *testing.T) {
	type want = analysistest.Want
	tests := []struct {
		rev   string
		wants []want
	}{
		// ARM64 bounds-checked a 32-bit shift count with a 64-bit compare.
		{"f2f369db0e^", []want{{File: "ARM64.rules", Rule: "(Rsh64x32 <t> x y) && !shiftIsBounded(v)", Message: `CMPconst \(arg 0\) reads 64 bits of y, but the match reads only 32`}}},
		{"f2f369db0e", []want{{File: "ARM64.rules", Rule: "(Rsh64x32 <t> x y) && !shiftIsBounded(v)", Absent: true}}},
		// LZCNTL counted the garbage above a 16- or 8-bit BitLen argument.
		{"5a103ca5e9^", []want{{File: "AMD64.rules", Rule: "(BitLen(32|16|8) <t> x) && buildcfg.GOAMD64 >= 3", Message: `LZCNTL \(arg 0\) reads 32 bits of x, but the match reads only (16|8) bits`}}},
		{"5a103ca5e9", []want{
			{File: "AMD64.rules", Rule: "(BitLen16 <t> x) && buildcfg.GOAMD64 >= 3", Absent: true},
			{File: "AMD64.rules", Rule: "(BitLen8 <t> x) && buildcfg.GOAMD64 >= 3", Absent: true},
		}},
		// LL/SC compare-and-swap compares a sign-extended word with all
		// 64 bits of the old value.
		{"0b2ad1d815^", []want{
			{File: "LOONG64.rules", Rule: "(AtomicCompareAndSwap(32|64) ...)", Message: `LoweredAtomicCas32 \(arg 1\) reads 64 bits of arg1, but the match reads only 32`},
			{File: "MIPS64.rules", Rule: "(AtomicCompareAndSwap(32|64) ...)", Message: `LoweredAtomicCas32 \(arg 1\) reads 64 bits of arg1`},
			{File: "RISCV64.rules", Rule: "(AtomicCompareAndSwap32 ...)", Message: `LoweredAtomicCas32 \(arg 1\) reads 64 bits of arg1`},
		}},
		{"0b2ad1d815", []want{
			{File: "LOONG64.rules", Rule: "(AtomicCompareAndSwap32 ptr old new mem)", Absent: true},
			{File: "MIPS64.rules", Rule: "(AtomicCompareAndSwap32 ptr old new mem)", Absent: true},
			{File: "RISCV64.rules", Rule: "(AtomicCompareAndSwap32 ptr old new mem)", Absent: true},
		}},
		// TSTconst tests 64 bits of what CMPWconst compared 32 of.
		{"91a2e921dd^", []want{{File: "ARM64.rules", Rule: "(LessThan (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTconst", Message: `TSTconst \(arg 0\) reads 64 bits of y, but the match reads only 32`}}},
		{"91a2e921dd", []want{{File: "ARM64.rules", Rule: "(LessThan (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTconst", Absent: true}}},
		// PPC64 bounds-checked 32-bit shift counts with the 64-bit CMPU.
		// The shift-lowering rework replaced the check with CMPWUconst.
		{"f98dd29910^", []want{{File: "PPC64.rules", Rule: "((Rsh64|Rsh64U|Lsh64)x32 x y)", Message: `CMPU \(arg 0\) reads 64 bits of y, but the match reads only 32`}}},
		{"f98dd29910", []want{{File: "PPC64.rules", Rule: "((Rsh64U|Lsh64)x32 <t> x y)", Absent: true}}},
	}
	for _, tt := range tests {
		t.Run(tt.rev, func(t *testing.T) {
			analysistest.RunRevision(t, tt.rev, demandedbits.Analyzer, tt.wants...)
		})
	}
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, demandedbits.Analyzer)
}
