package rulelint_test

import (
	"path/filepath"
	"regexp"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/analyzers/rulelint"
)

func Test(t *testing.T) {
	analysistest.Run(t, "testdata", rulelint.Analyzer)
}

func TestSurvey(t *testing.T) {
	analysistest.Survey(t, rulelint.Analyzer)
}

func TestHistorical(t *testing.T) {
	type test struct {
		rev   string // the fix; the bug is at rev^
		file  string
		rules []string
		msg   string
	}
	tests := []test{
		// A fixed one-arg match of variadic StructMake (issue 74908).
		{"72e8237cc1", "generic.rules", []string{"(IMake _typ (StructMake val)) => imakeOfStructMake(v)"}, `did you mean \(StructMake ___\)`},
		// ArrayMake1 of a zero-sized [1]T (issue 80543).
		{"5bac01f52f", "generic.rules", []string{"(Load <t> ptr mem) && t.IsArray() && t.NumElem() == 1 &&"}, `needs a t.Size\(\) > 0 condition`},
		// IsPtr instead of IsPtrShaped (issue 63505).
		{"eb832afb23", "dec.rules", []string{
			"(StructSelect [0] x) && x.Type.IsPtr",
			"(ArraySelect [0] x) && x.Type.IsPtr",
			"(ArrayMake1 x) && x.Type.IsPtr",
			"(StructMake1 x) && x.Type.IsPtr",
		}, `use IsPtrShaped`},
		// A new type symbol reference not marked as used (issue 75203).
		{"d767064170", "generic.rules", []string{
			"(Load <t> (OffPtr [off] (Addr {s} sb) ) _) && t.IsPtr() && isPtrElem(s, off)",
			"(Load <t> (OffPtr [off] (Convert (Addr {s} sb) _) ) _) && t.IsPtr() && isPtrElem(s, off)",
			"(Load <t> (OffPtr [off] (ITab (IMake (Addr {s} sb) _))) _) && t.IsPtr() && isPtrElem(s, off)",
			"(Load <t> (OffPtr [off] (ITab (IMake (Convert (Addr {s} sb) _) _))) _) && t.IsPtr() && isPtrElem(s, off)",
		}, `ptrElem\(s, off\) synthesizes a symbol`},
		// c & -1<<63 == 0 tests bit 0, not the sign bit. The rewrite of
		// these rules in 854e892ce1 fixed it in passing.
		{"854e892ce1", "S390X.rules", []string{
			"(OR (SLDconst [63] (SRDconst [63] (LGDR x))) (MOVDconst [c])) && c & -1<<63 == 0",
			"(OR (AND (MOVDconst [-1<<63]) (LGDR x)) (MOVDconst [c])) && c & -1<<63 == 0",
		}, `c & -1 << 63 means \(c & -1\) << 63`},
	}
	for _, tt := range tests {
		t.Run(tt.rev, func(t *testing.T) {
			var wants []analysistest.Want
			for _, r := range tt.rules {
				wants = append(wants, analysistest.Want{File: tt.file, Rule: r, Message: tt.msg})
			}
			analysistest.RunRevision(t, tt.rev+"^", rulelint.Analyzer, wants...)
			diags := analysistest.RunRevision(t, tt.rev, rulelint.Analyzer)
			for _, d := range diags {
				if filepath.Base(d.Pos.File) == tt.file && regexp.MustCompile(tt.msg).MatchString(d.Message) {
					t.Errorf("%s: still reported after the fix: %v", tt.rev, d)
				}
			}
		})
	}
}

// Before the Empty op (b48b2002fe), zero-sized StructMake and ArrayMake1
// were legal, and rules made them deliberately.
func TestEmptyMakeBeforeEmpty(t *testing.T) {
	analysistest.RunRevision(t, "b48b2002fe^", rulelint.Analyzer,
		analysistest.Want{File: "generic.rules", Rule: "(StructSelect (IData x)) && v.Type.Size() == 0 && v.Type.IsStruct() => (StructMake)", Absent: true},
	)
}
