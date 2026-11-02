package typecheck_test

import (
	"go/types"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

func checkSrc(t *testing.T, name, src string) (*typecheck.Result, []*rules.Rule) {
	t.Helper()
	tab, err := ops.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	c := rules.Parse(tab, map[string][]byte{name: []byte(src)})
	for _, err := range c.Errors {
		t.Fatal(err)
	}
	res, err := typecheck.Check(c.Sets[0])
	if err != nil {
		t.Fatal(err)
	}
	return res, c.Sets[0].Rules
}

// typeName formats t without package paths.
func typeName(t types.Type) string {
	return types.TypeString(t, func(p *types.Package) string { return p.Name() })
}

func TestTypes(t *testing.T) {
	res, rs := checkSrc(t, "AMD64.rules", `
(ADDQ x (MOVQconst [c])) && ssa.Is32Bit(c) && !t.IsPtr() => (ADDQconst <t> [int32(c)] x)
(MOVLload [off1] {sym} (ADDQconst [off2] ptr) mem) && ssa.Is32Bit(int64(off1)+int64(off2)) => (MOVLload [off1+off2] {sym} ptr mem)
(SETL (InvertFlags x)) => (SETG x)
(CMPQconst (MOVQconst [x]) [y]) && x == int64(y) => (FlagEQ)
(MOVBstoreconst [sc] {s} (ADDQconst [off] ptr) mem) && ssa.ValAndOff(sc).CanAdd32(off) => (MOVBstoreconst [ssa.ValAndOff(sc).AddOffset32(off)] {s} ptr mem)
(EQ (TESTQ x x) yes no) && x.Uses == 1 => (EQ (TESTQ x x) yes no)
`[1:])
	// The first rule uses t, which the match doesn't bind.
	if errs := res.Rule(rs[0]).Errors; len(errs) != 2 || !strings.Contains(errs[0].Error(), "undefined: t") {
		t.Errorf("rule 0 errors = %v", errs)
	}
	for _, r := range rs[1:] {
		for _, err := range res.Rule(r).Errors {
			t.Errorf("%s: %v", r.Text, err)
		}
	}

	tr := res.Rule(rs[0])
	vars := map[string]string{}
	for name, v := range tr.Vars {
		vars[name] = typeName(v.Type())
	}
	if vars["x"] != "*ssa.Value" || vars["c"] != "int64" {
		t.Errorf("vars = %v", vars)
	}
	if got := typeName(res.Info.TypeOf(res.Rule(rs[1]).Cond)); got != "bool" {
		t.Errorf("cond type %s", got)
	}
	add := rs[0].Result
	if got := typeName(res.Info.TypeOf(tr.Expr(add, typecheck.AuxInt))); got != "int32" {
		t.Errorf("result auxint type %s", got)
	}
	if id := tr.Expr(rs[0].Match.Args[1], typecheck.AuxInt); id == nil || typeName(res.Info.TypeOf(id)) != "int64" {
		t.Errorf("match auxint expr %v", id)
	}

	tr = res.Rule(rs[1])
	for name, want := range map[string]string{"off1": "int32", "off2": "int32", "sym": "ssa.Sym", "ptr": "*ssa.Value", "mem": "*ssa.Value"} {
		if v := tr.Vars[name]; v == nil || typeName(v.Type()) != want {
			t.Errorf("%s: got %v, want %s", name, v, want)
		}
	}
	if got := typeName(res.Info.TypeOf(tr.Expr(rs[1].Result, typecheck.AuxInt))); got != "int32" {
		t.Errorf("off1+off2 type %s", got)
	}

	tr = res.Rule(rs[3])
	if typeName(tr.Vars["x"].Type()) != "int64" || typeName(tr.Vars["y"].Type()) != "int32" {
		t.Errorf("x, y = %v, %v", tr.Vars["x"], tr.Vars["y"])
	}
	tr = res.Rule(rs[4])
	if got := typeName(tr.Vars["sc"].Type()); got != "ssa.ValAndOff" {
		t.Errorf("sc type %s", got)
	}
	if tr := res.Rule(rs[5]); typeName(tr.Vars["x"].Type()) != "*ssa.Value" || tr.Cond == nil {
		t.Errorf("block rule vars %v", tr.Vars)
	}
}

func TestTypeErrors(t *testing.T) {
	res, rs := checkSrc(t, "generic.rules", `
(Neg8 (Const8 [c])) => (Const8 [300])
(Neg16 (Const16 [c])) && c => (Const16 [-c])
(Neg32 (Const32 <t> [c])) => (Const32 <c> [-c])
(Neg64 (Const64 [c])) => (Const64 [-c])
(Addr {_} (SB)) && false => (ConstNil)
(Com8 (Const8 [c])) && c == 0 => (Const8 [-1])
`[1:])
	want := []string{"overflows", "non-boolean", "not a type|cannot use", "", "", ""}
	for i, r := range rs {
		var msgs []string
		for _, err := range res.Rule(r).Errors {
			msgs = append(msgs, err.Error())
		}
		got := strings.Join(msgs, "; ")
		ok := want[i] == "" && got == ""
		for _, w := range strings.Split(want[i], "|") {
			ok = ok || w != "" && strings.Contains(got, w)
		}
		if !ok {
			t.Errorf("%s: errors %q, want %q", r.Text, got, want[i])
		}
	}
	// The untyped constant -1 is converted to int8.
	if x := res.Rule(rs[5]).Expr(rs[5].Result, typecheck.AuxInt); typeName(res.Info.TypeOf(x)) != "int8" {
		t.Errorf("-1 has type %v", res.Info.TypeOf(x))
	}
}
