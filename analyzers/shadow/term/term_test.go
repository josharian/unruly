package term

import (
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
)

func TestSubst(t *testing.T) {
	got := Subst("x.Type.Size() + c*int64(x.AuxInt)", func(name string) (string, bool) {
		switch name {
		case "x":
			return "y", true
		case "c":
			return "-1", true
		}
		return "", false
	})
	if want := "y.Type.Size() + (-1)*int64(y.AuxInt)"; got != want {
		t.Errorf("got %q, want %q", got, want)
	}
}

func TestFacts(t *testing.T) {
	f := NewFacts()
	f.UseHelpers(analysistest.Tables(t).Dir)
	f.Assume("c >= 0 && c <= 31 && ssa.CanonLessThan(x, y) && !ssa.IsVolatile(p) && ssa.IsSamePtr(p, q)")
	for _, c := range []string{
		"c < 32", "c != -1", "c >= 0 || z", "ssa.Clobber(x, y)",
		"!ssa.IsVolatile(p)", "ssa.OneBit(int64(4))", "ssa.Is32Bit(-0)",
	} {
		if !f.Implies(c) {
			t.Errorf("Implies(%q) = false", c)
		}
	}
	for _, c := range []string{
		"c < 0", "c == 40", "ssa.CanonLessThan(y, x)", "ssa.IsVolatile(p)",
		"ssa.Disjoint1(q, 8, p, 8)", "ssa.OneBit(int8(0))",
	} {
		if !f.Refutes(c) {
			t.Errorf("Refutes(%q) = false", c)
		}
	}
	for _, c := range []string{"c < 31", "d < 32", "x.Uses == 1", "ssa.CanonLessThan(x, z)"} {
		if f.Implies(c) || f.Refutes(c) {
			t.Errorf("%q decided, want unknown", c)
		}
	}
}
