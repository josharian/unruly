package typewidth_test

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/typewidth"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", typewidth.Analyzer)
}

func TestHistorical(t *testing.T) {
	type want = analysistest.Want
	tests := []struct {
		rev   string
		wants []want
	}{
		// Canonicalized shift counts were Const64s typed with the
		// shift's own (narrower) type.
		{"8dcb3171f6^", []want{
			{File: "generic.rules", Rule: "(Lsh32x32  <t> x (Const32 [c])) => (Lsh32x64  x (Const64 <t>", Message: `\(Const64 <t> \.\.\.\) gives a 64-bit integer result the type t, a 32-bit integer`},
			{File: "generic.rules", Rule: "(Rsh8Ux8   <t> x (Const8  [c])) => (Rsh8Ux64  x (Const64 <t>", Message: `the type t, an 8-bit integer`},
			{File: "generic.rules", Rule: "(Lsh64x32  <t> x (Const32 [c])) => (Lsh64x64  x (Const64 <t>", Absent: true},
		}},
		{"8dcb3171f6", []want{
			{File: "generic.rules", Rule: "(Lsh32x32  x (Const32 [c])) => (Lsh32x64  x (Const64", Absent: true},
		}},
		// A rotate count rewritten to Const32 kept the Const64's type.
		{"6b3800e1dd^", []want{
			{File: "generic.rules", Rule: "(RotateLeft32 x (Const64 <t> [c])) && config.PtrSize == 4", Message: `\(Const32 <t> \.\.\.\) gives a 32-bit integer result the type t, a 64-bit integer`},
		}},
		{"6b3800e1dd", []want{
			{File: "generic.rules", Rule: "(RotateLeft(64|32|16|8) x (Const64 [c])) && config.PtrSize == 4", Absent: true},
		}},
		// A Const64 multiplier of a Mul64 was typed UInt32.
		{"819c53c25f^", []want{
			{File: "divmod.rules", Rule: "(Const64 <typ.UInt32> [int64(umagic32(c).m)])", Message: `\(Const64 <typ.UInt32> \.\.\.\) gives a 64-bit integer result the type typ.UInt32`},
		}},
		{"819c53c25f", []want{
			{File: "divmod.rules", Rule: "(Mul64 <typ.UInt64> (ZeroExt32to64 x) (Const64 <typ.UInt64> [int64(umagic32(c).m)])", Absent: true},
		}},
		// IsInBounds of an 8-bit index and a 64-bit length never matches.
		{"d9884eed65^", []want{
			{File: "generic.rules", Rule: "(IsInBounds                (Rsh8Ux64  _ (Const64 [c]))  (Const64 [d]))", Message: `IsInBounds's arguments always have the same type, so they are never Rsh8Ux64 \(an 8-bit integer\) and Const64`},
		}},
		{"d9884eed65", []want{
			{File: "generic.rules", Rule: "(IsInBounds                (Rsh8Ux64  _ (Const64 [c]))  (Const8  [d]))", Absent: true},
		}},
	}
	for _, tt := range tests {
		t.Run(tt.rev, func(t *testing.T) {
			analysistest.RunRevision(t, tt.rev, typewidth.Analyzer, tt.wants...)
		})
	}
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, typewidth.Analyzer)
}
