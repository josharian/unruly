package extelim_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/extelim"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", extelim.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, extelim.Analyzer)
}

type W = analysistest.Want

// TestHistorical checks the fixes of extension-elimination bugs: each
// diagnostic is reported in the fix's parent and not in the fix.
//
// Not covered: fixes from before typed rules (3f04db41a8, 755b36aa53,
// 1566bf9025, 1e0819101b, 9613a638a9, 094992e22a, ddf807fce8); d5e5b14305,
// whose rule relies on mergePPC64AndRlwinm, a helper this package does
// not model; 3c8b5e6738, a constant of the wrong width rather than a
// wrong extension; and a4bac74d2a, which moved loong64's elisions to
// latelower before any rule in its pass could rewrite their arguments.
func TestHistorical(t *testing.T) {
	for _, tt := range []struct {
		rev    string
		before W // in rev's parent
		after  W // absent in rev
	}{
		{"90a11e921b", // ARM64: an elision justified by the type
			W{File: "ARM64.rules", Rule: "(MOVBUreg x) && x.Type.IsBoolean() => (MOVDreg x)", Message: "constrains only its type"},
			W{File: "ARM64.rules", Rule: "(MOVBUreg x:((Equal|NotEqual|LessThan|LessThanU|LessThanF"},
		},
		{"10a908733a", // RISCV64: a W op's result has an unsigned type
			W{File: "RISCV64.rules", Rule: "(MOVWreg x:(MULW _ _)) => (MOVDreg x)", Message: `MULW can have type uint32 .* restored zero-extended`},
			W{File: "RISCV64.rules", Rule: "(MOVWreg x:(MULW _ _)) && (x.Type.Size() == 8"},
		},
		{"a9bedc36a5", // ARM64: a rewrite of MULW loses the zeroed upper half
			W{File: "ARM64.rules", Rule: "(MOVWUreg x) && zeroUpper32Bits(x, 3) => x", Message: `may rewrite that MULW later in the same pass into \(NEG x\)`},
			W{File: "ARM64.rules", Rule: "(MOVWUreg x) && zeroUpper32Bits(x, 3) => x", Message: `into \(NEG x\)`},
		},
		{"a46ecdca36", // ARM64 and AMD64: elisions in the main lowering pass
			W{File: "ARM64.rules", Rule: "(MOVWUreg x:(MOVWUreg _)) => (MOVDreg x)", Message: "may rewrite that MOVWUreg later in the same pass into x"},
			W{File: "ARM64latelower.rules", Rule: "(MOVWUreg x:(MOVWUreg _)) => (MOVDreg x)", Message: "may rewrite"},
		},
		{"a46ecdca36",
			W{File: "AMD64.rules", Rule: "(MOVLQZX x) && zeroUpper32Bits(x,3) => x", Message: "may rewrite that ADDLconst later in the same pass into x"},
			W{File: "AMD64latelower.rules", Rule: "(MOVLQZX x) && zeroUpper32Bits(x,3) => x"},
		},
		{"a7e331e671", // MIPS64: a read-only fold of a signed load zero-extends
			W{File: "MIPS64.rules", Rule: "(MOVBreg x:(MOVBload _ _)) => (MOVVreg x)", Message: `may rewrite that MOVBload later in the same pass into \(MOVVconst \[int64\(read8`},
			W{File: "MIPS64.rules", Rule: "(MOVBreg x:(MOVBload _ _)) => (MOVVreg x)", Message: "may rewrite"},
		},
		{"8fd0f83552", // RISCV64: a constant fold that forgets to sign-extend
			W{File: "RISCV64.rules", Rule: "(MOVBreg (MOVDconst [c])) => (MOVDconst [int64(c)])", Message: "match and result differ when c=0x80"},
			W{File: "RISCV64.rules", Rule: "(MOVBreg (MOVDconst [c])) => (MOVDconst [int64(int8(c))])"},
		},
		{"5e4000ad7f", // PPC64: a sign extension dropped under a mask
			W{File: "PPC64.rules", Line: 598, Message: "match and result differ"},
			W{File: "PPC64.rules", Rule: "(Select0 (ANDCCconst [c] (MOVBZreg x))) => (Select0 (ANDCCconst [c&0xFF] x))"},
		},
	} {
		t.Run(tt.rev, func(t *testing.T) {
			analysistest.RunRevision(t, tt.rev+"^", extelim.Analyzer, tt.before)
			tt.after.Absent = true
			if tt.after.Message == "" {
				tt.after.Message = tt.before.Message
			}
			analysistest.RunRevision(t, tt.rev, extelim.Analyzer, tt.after)
		})
	}
}
