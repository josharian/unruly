package mem_test

import (
	"testing"

	"github.com/josharian/unruly/analyzers/memchain/mem"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/rules"
)

func TestOps(t *testing.T) {
	c, err := rules.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	tab := mem.Ops(c)
	tests := []struct {
		arch, op string
		want     mem.OpInfo
	}{
		{"generic", "Load", mem.OpInfo{Mem: true, Out: mem.OutNone, Read: true}},
		{"generic", "Store", mem.OpInfo{Mem: true, Out: mem.OutMem}},
		{"generic", "Move", mem.OpInfo{Mem: true, Out: mem.OutMem, Read: true}},
		{"generic", "StaticLECall", mem.OpInfo{Mem: true, Out: mem.OutResults, Read: true}},
		{"generic", "AtomicLoad32", mem.OpInfo{Mem: true, Out: mem.OutTuple, Read: true}},
		{"generic", "Add64", mem.OpInfo{Out: mem.OutNone}},
		{"AMD64", "MOVQload", mem.OpInfo{Mem: true, Out: mem.OutNone, Read: true}},
		{"AMD64", "ADDQload", mem.OpInfo{Mem: true, Out: mem.OutNone, Read: true}},
		{"AMD64", "MOVQstore", mem.OpInfo{Mem: true, Out: mem.OutMem}},
		{"AMD64", "ADDQmodify", mem.OpInfo{Mem: true, Out: mem.OutMem, Read: true}},
		{"AMD64", "XADDLlock", mem.OpInfo{Mem: true, Out: mem.OutTuple, Read: true}},
		{"AMD64", "LoweredZero", mem.OpInfo{Mem: true, Out: mem.OutMem}},
		{"AMD64", "CALLstatic", mem.OpInfo{Mem: true, Out: mem.OutResults, Read: true}},
		{"AMD64", "LEAQ", mem.OpInfo{Out: mem.OutNone}},
		{"AMD64", "AddTupleFirst32", mem.OpInfo{Out: mem.OutTuple}},
		{"ARM64", "STLR", mem.OpInfo{Mem: true, Out: mem.OutMem}},
		{"ARM64", "LoweredAtomicAdd64", mem.OpInfo{Mem: true, Out: mem.OutTuple, Read: true}},
		{"ARM64", "MOVDloadidx", mem.OpInfo{Mem: true, Out: mem.OutNone, Read: true}}, // no symEffect
		{"PPC64", "MOVDBRload", mem.OpInfo{Mem: true, Out: mem.OutNone, Read: true}},
		{"386", "CALLstatic", mem.OpInfo{Mem: true, Out: mem.OutResults, Read: true}}, // argLength 1
		{"MIPS64", "CALLclosure", mem.OpInfo{Mem: true, Out: mem.OutResults, Read: true}},
	}
	for _, tt := range tests {
		a := c.Ops.Arch(tt.arch)
		op := a.LookupOp(tt.op)
		if op == nil {
			t.Errorf("%s: no op %s", tt.arch, tt.op)
			continue
		}
		if got := tab.Op(op); got != tt.want {
			t.Errorf("%s.%s = %+v, want %+v", tt.arch, tt.op, got, tt.want)
		}
	}
}
