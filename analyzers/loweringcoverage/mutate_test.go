package loweringcoverage

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
)

// mutate returns the tree's rules files, with old replaced by new in
// the file name. These tests check the analyzer against the real rules
// with one defect introduced.
func mutate(t *testing.T, name, old, new string) map[string]string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join(analysistest.Tables(t).Dir, "*.rules"))
	if err != nil {
		t.Fatal(err)
	}
	files := map[string]string{}
	for _, p := range paths {
		b, err := os.ReadFile(p)
		if err != nil {
			t.Fatal(err)
		}
		files[filepath.Base(p)] = string(b)
	}
	s := files[name]
	if strings.Count(s, old) != 1 {
		t.Skipf("%s no longer has exactly one %q", name, old)
	}
	files[name] = strings.Replace(s, old, new, 1)
	return files
}

// Intrinsics enable the internal/runtime/atomic Load8 and Store8
// intrinsics on MIPS, so the atomic ops they emit must be lowered (as in
// ec10e6f364, which added the missing MIPS lowering).
func TestIntrinsicReach(t *testing.T) {
	intrinsicsAnywhere = true
	defer func() { intrinsicsAnywhere = false }()
	analysistest.RunFiles(t, mutate(t, "MIPS.rules",
		"(AtomicLoad(8|32) ...) => (LoweredAtomicLoad(8|32) ...)",
		"(AtomicLoad32 ...) => (LoweredAtomicLoad32 ...) // want `intrinsic \\S+ on MIPS emits AtomicLoad8, but MIPS has no rule lowering AtomicLoad8`",
	), Analyzer)
}

// 386 lowers Ctz16, and prove replaces Ctz16 by Ctz16NonZero (as in
// 8d5197d818, which added the missing 386 lowering).
func TestSubstitutionReach(t *testing.T) {
	intrinsicsAnywhere = true
	defer func() { intrinsicsAnywhere = false }()
	files := mutate(t, "386.rules", "(Ctz16NonZero ...) => (BSFL ...)\n", "")
	files["386.rules"] = strings.Replace(files["386.rules"],
		"(Ctz16 x) => (BSFL (ORLconst <typ.UInt32> [0x10000] x))",
		"(Ctz16 x) => (BSFL (ORLconst <typ.UInt32> [0x10000] x)) // want `386 lowers Ctz16, which prove.go:ctzNonZeroOp replaces by Ctz16NonZero, but has no rule for Ctz16NonZero`", 1)
	analysistest.RunFiles(t, files, Analyzer)
}

// A Zero lowering that writes the wrong bytes.
func TestBytesMutation(t *testing.T) {
	analysistest.RunFiles(t, mutate(t, "AMD64.rules",
		"(Zero [3] destptr mem) =>\n\t(MOVBstoreconst [ssa.MakeValAndOff(0,2)] destptr",
		"(Zero [3] destptr mem) => // want `AMD64 lowering of s=3 t.Alignment\\(\\)=1: MOVBstoreconst writes bytes \\[3,4\\), outside \\[0,3\\)`\n\t(MOVBstoreconst [ssa.MakeValAndOff(0,3)] destptr",
	), Analyzer)
}

// Without the rule that lowers OffPtr of SP to MOVDaddr, ARM64 would
// lower it to an add, which regalloc may spill.
func TestRematMutation(t *testing.T) {
	analysistest.RunFiles(t, mutate(t, "ARM64.rules",
		"(OffPtr [off] ptr:(SP)) && ssa.Is32Bit(off) => (MOVDaddr [int32(off)] ptr)\n(OffPtr [off] ptr) => (ADDconst [off] ptr)",
		"(OffPtr [off] ptr) => (ADDconst [off] ptr) // want `\\(OffPtr \\[8\\] \\(SP\\)\\) lowers to .*, which is not rematerializeable`",
	), Analyzer)
}
