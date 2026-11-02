package ops_test

import (
	"testing"

	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
)

func TestSIMDGenericOps(t *testing.T) {
	tab, err := ops.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	n := 0
	for _, op := range tab.Generic.Ops {
		if op.SIMD {
			n++
		}
	}
	if add := tab.Generic.LookupOp("AddFloat32x4"); add != nil && !add.SIMD {
		t.Errorf("AddFloat32x4 not marked SIMD")
	}
	if tab.Generic.LookupOp("Add64").SIMD {
		t.Errorf("Add64 marked SIMD")
	}
	t.Logf("%d of %d generic ops are SIMD", n, len(tab.Generic.Ops))
}
