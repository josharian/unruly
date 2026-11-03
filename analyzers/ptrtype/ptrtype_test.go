package ptrtype_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/ptrtype"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", ptrtype.Analyzer)
}

// RISCV64's pointer difference typed as a pointer: fixed by 1ed30ca537.
func TestHistoricalEqPtr(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		return []analysistest.Want{
			{File: "RISCV64.rules", Rule: "(EqPtr x y) =>", Message: `^SUB computes a non-pointer but is typed <x.Type>`, Absent: absent},
			{File: "RISCV64.rules", Rule: "(NeqPtr x y) =>", Message: `^SUB computes a non-pointer but is typed <x.Type>`, Absent: absent},
		}
	}
	analysistest.RunRevision(t, "1ed30ca537^", ptrtype.Analyzer, want(false)...)
	analysistest.RunRevision(t, "1ed30ca537", ptrtype.Analyzer, want(true)...)
}

// AMD64latelower's LEA splitting typed y+c like the possibly-pointer LEA:
// introduced by f9cf2c4d04, reverted by 96d2e41617.
func TestHistoricalLEASplit(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		return []analysistest.Want{
			{File: "AMD64latelower.rules", Rule: "&&  isPtr(x.Type) && c != 0", Message: `^\(ADDQconst <t> \.\.\.\) is typed like the matched LEAQ1, which may be a pointer, but does not contain its pointer operand x;`, Absent: absent},
			{File: "AMD64latelower.rules", Rule: "&& !isPtr(x.Type) && c != 0", Message: `^\(ADDQconst <t> \.\.\.\) is typed like the matched LEAQ1, which may be a pointer, but does not contain its pointer operand y;`, Absent: absent},
		}
	}
	analysistest.RunRevision(t, "96d2e41617^", ptrtype.Analyzer, want(false)...)
	analysistest.RunRevision(t, "96d2e41617", ptrtype.Analyzer, want(true)...)
}

// Folding a typed nil into an add-immediate: fixed by 21f434058c.
func TestHistoricalNilFold(t *testing.T) {
	want := func(absent bool) []analysistest.Want {
		ws := []analysistest.Want{
			{File: "ARM64.rules", Rule: "(ADD x (MOVDconst", Message: `^ADD of a MOVDconst, which may be a typed nil`},
			{File: "PPC64.rules", Rule: "(ADD x (MOVDconst", Message: `^ADD of a MOVDconst, which may be a typed nil`},
			{File: "S390X.rules", Rule: "(ADD x (MOVDconst", Message: `^ADD of a MOVDconst, which may be a typed nil`},
			{File: "MIPS64.rules", Rule: "(ADDV x (MOVVconst", Message: `^ADDV of a MOVVconst, which may be a typed nil`},
			{File: "Wasm.rules", Rule: "(I64Add x (I64Const", Message: `^I64Add of a I64Const, which may be a typed nil`},
		}
		// The RISCV64 rule's text changes with the fix.
		riscv := "(ADD (MOVDconst [val]) x) && is32Bit(val) =>"
		if absent {
			riscv = "(ADD (MOVDconst <t> [val]) x) && is32Bit(val) && !t.IsPtr() =>"
		}
		ws = append(ws, analysistest.Want{File: "RISCV64.rules", Rule: riscv, Message: `^ADD of a MOVDconst, which may be a typed nil`})
		for i := range ws {
			ws[i].Absent = absent
		}
		return ws
	}
	analysistest.RunRevision(t, "21f434058c^", ptrtype.Analyzer, want(false)...)
	analysistest.RunRevision(t, "21f434058c", ptrtype.Analyzer, want(true)...)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, ptrtype.Analyzer)
}
