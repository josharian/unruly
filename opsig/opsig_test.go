package opsig_test

import (
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
)

func tables(t *testing.T) *ops.Tables {
	t.Helper()
	tab, err := ops.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	return tab
}

// TestComplete checks that every generic op has a signature that matches
// its arity and default type.
func TestComplete(t *testing.T) {
	for _, op := range tables(t).Generic.Ops {
		s, ok := opsig.Lookup(op)
		if !ok {
			t.Errorf("%s (argLength %d, typ %q): no signature", op, op.ArgLength, op.Typ)
			continue
		}
		if op.ArgLength < 0 {
			if s.Variadic == nil || len(s.Args) != 0 {
				t.Errorf("%s: variadic, but Variadic is %v and Args has %d elements", op, s.Variadic, len(s.Args))
			}
		} else if s.Variadic != nil || len(s.Args) != int(op.ArgLength) {
			t.Errorf("%s: argLength %d, but signature has %d Args (Variadic %v)", op, op.ArgLength, len(s.Args), s.Variadic)
		}
		if s.SIMD != op.SIMD {
			t.Errorf("%s: SIMD is %v, op.SIMD is %v", op, s.SIMD, op.SIMD)
		}
		if op.Typ == "" {
			continue
		}
		want, ok := typOperand(op.Typ)
		if !ok {
			t.Errorf("%s: unrecognized default type %q", op, op.Typ)
			continue
		}
		if !reflect.DeepEqual(s.Result, want) {
			t.Errorf("%s: result is %+v; default type %q implies %+v", op, s.Result, op.Typ, want)
		}
	}
}

// typOperand returns the Operand that an op's default type implies.
// genericOps.go spells some types oddly, as in "bool" and "(Uint64, Mem)".
func typOperand(typ string) (opsig.Operand, bool) {
	if strings.HasPrefix(typ, "(") && strings.HasSuffix(typ, ")") {
		a, b, ok := strings.Cut(typ[1:len(typ)-1], ",")
		if !ok {
			return opsig.Operand{}, false
		}
		x, ok1 := typOperand(strings.TrimSpace(a))
		y, ok2 := typOperand(strings.TrimSpace(b))
		return opsig.Operand{Kind: opsig.Tuple, Elems: []opsig.Operand{x, y}}, ok1 && ok2
	}
	switch typ {
	case "Bool", "bool":
		return opsig.Operand{Kind: opsig.Bool}, true
	case "Int":
		return opsig.Operand{Kind: opsig.Int, Sign: opsig.Signed}, true
	case "Uintptr", "BytePtr":
		return opsig.Operand{Kind: opsig.Ptr}, true
	case "Mem":
		return opsig.Operand{Kind: opsig.Mem}, true
	case "Flags":
		return opsig.Operand{Kind: opsig.Flags}, true
	case "Void":
		return opsig.Operand{Kind: opsig.Void}, true
	case "Float32", "Float64":
		w, _ := strconv.Atoi(typ[len("Float"):])
		return opsig.Operand{Kind: opsig.Float, Width: w}, true
	}
	for _, p := range []struct {
		prefix string
		sign   opsig.Sign
	}{{"Int", opsig.Signed}, {"UInt", opsig.Unsigned}, {"Uint", opsig.Unsigned}} {
		if w, err := strconv.Atoi(strings.TrimPrefix(typ, p.prefix)); err == nil && strings.HasPrefix(typ, p.prefix) {
			switch w {
			case 8, 16, 32, 64:
				return opsig.Operand{Kind: opsig.Int, Width: w, Sign: p.sign}, true
			}
		}
	}
	return opsig.Operand{}, false
}

func TestExamples(t *testing.T) {
	tab := tables(t)
	lookup := func(name string) opsig.Sig {
		t.Helper()
		op := tab.Generic.Op(name)
		if op == nil {
			t.Fatalf("no generic op %s", name)
		}
		s, ok := opsig.Lookup(op)
		if !ok {
			t.Fatalf("no signature for %s", name)
		}
		return s
	}
	i := func(w int, s opsig.Sign) opsig.Operand { return opsig.Operand{Kind: opsig.Int, Width: w, Sign: s} }
	f := func(w int) opsig.Operand { return opsig.Operand{Kind: opsig.Float, Width: w} }
	boolean := opsig.Operand{Kind: opsig.Bool}
	mem := opsig.Operand{Kind: opsig.Mem}
	ptr := opsig.Operand{Kind: opsig.Ptr}
	anyv := opsig.Operand{Kind: opsig.Any}

	tests := []struct {
		op     string
		result opsig.Operand
		args   []opsig.Operand
	}{
		{"Add32", i(32, opsig.SignAny), []opsig.Operand{i(32, opsig.SignAny), i(32, opsig.SignAny)}},
		{"Rsh32Ux64", i(32, opsig.Unsigned), []opsig.Operand{i(32, opsig.Unsigned), i(64, opsig.Unsigned)}},
		{"Rsh32x64", i(32, opsig.Signed), []opsig.Operand{i(32, opsig.Signed), i(64, opsig.Unsigned)}},
		{"Lsh8x16", i(8, opsig.SignAny), []opsig.Operand{i(8, opsig.SignAny), i(16, opsig.Unsigned)}},
		{"ZeroExt8to32", i(32, opsig.Unsigned), []opsig.Operand{i(8, opsig.Unsigned)}},
		{"SignExt16to64", i(64, opsig.Signed), []opsig.Operand{i(16, opsig.Signed)}},
		{"Trunc64to16", i(16, opsig.SignAny), []opsig.Operand{i(64, opsig.SignAny)}},
		{"Cvt32Fto64F", f(64), []opsig.Operand{f(32)}},
		{"Cvt64Uto32F", f(32), []opsig.Operand{i(64, opsig.Unsigned)}},
		{"Cvt64Fto32", i(32, opsig.Signed), []opsig.Operand{f(64)}},
		{"Less64U", boolean, []opsig.Operand{i(64, opsig.Unsigned), i(64, opsig.Unsigned)}},
		{"Leq16", boolean, []opsig.Operand{i(16, opsig.Signed), i(16, opsig.Signed)}},
		{"Hmul32u", i(32, opsig.Unsigned), []opsig.Operand{i(32, opsig.Unsigned), i(32, opsig.Unsigned)}},
		{"Div64u", i(64, opsig.Unsigned), []opsig.Operand{i(64, opsig.Unsigned), i(64, opsig.Unsigned)}},
		{"Mod8", i(8, opsig.Signed), []opsig.Operand{i(8, opsig.Signed), i(8, opsig.Signed)}},
		{"Ctz64", i(0, opsig.SignAny), []opsig.Operand{i(64, opsig.SignAny)}},
		{"BitLen8", i(0, opsig.SignAny), []opsig.Operand{i(8, opsig.SignAny)}},
		{"Load", anyv, []opsig.Operand{ptr, mem}},
		{"CondSelect", anyv, []opsig.Operand{anyv, anyv, boolean}},
		{"Signmask", i(32, opsig.Signed), []opsig.Operand{i(32, opsig.Signed)}},
		{"PanicExtend", mem, []opsig.Operand{i(32, opsig.SignAny), i(32, opsig.SignAny), i(0, opsig.SignAny), mem}},
		{"ComplexReal", f(0), []opsig.Operand{{Kind: opsig.Complex}}},
		{"Div128u",
			opsig.Operand{Kind: opsig.Tuple, Elems: []opsig.Operand{i(64, opsig.Unsigned), i(64, opsig.Unsigned)}},
			[]opsig.Operand{i(64, opsig.Unsigned), i(64, opsig.Unsigned), i(64, opsig.Unsigned)}},
		{"Mul64uover",
			opsig.Operand{Kind: opsig.Tuple, Elems: []opsig.Operand{i(64, opsig.Unsigned), boolean}},
			[]opsig.Operand{i(64, opsig.Unsigned), i(64, opsig.Unsigned)}},
		{"Cvt16toMask8x16", opsig.Operand{Kind: opsig.Vector}, []opsig.Operand{i(16, opsig.SignAny)}},
		{"BroadcastFloat32s", opsig.Operand{Kind: opsig.Vector}, []opsig.Operand{f(32)}},
	}
	for _, tt := range tests {
		s := lookup(tt.op)
		if !reflect.DeepEqual(s.Result, tt.result) || !reflect.DeepEqual(s.Args, tt.args) || s.Variadic != nil || s.SIMD {
			t.Errorf("%s: got %+v, want result %+v, args %+v", tt.op, s, tt.result, tt.args)
		}
	}

	if s := lookup("Phi"); s.Variadic == nil || !reflect.DeepEqual(*s.Variadic, anyv) || s.Result.Kind != opsig.Any {
		t.Errorf("Phi: got %+v", s)
	}

	for _, op := range tab.Generic.Ops {
		if !op.SIMD {
			continue
		}
		s, ok := opsig.Lookup(op)
		if !ok || !s.SIMD || s.Result.Kind != opsig.Unknown {
			t.Errorf("%s: got %+v, %v; want an undescribed SIMD signature", op, s, ok)
		}
		break
	}

	if amd64 := tab.Arch("AMD64"); amd64 != nil {
		if s, ok := opsig.Lookup(amd64.Op("ADDQ")); ok {
			t.Errorf("Lookup(AMD64 ADDQ) = %+v, want false", s)
		}
	}
}
