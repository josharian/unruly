package facts_test

import (
	"go/ast"
	"go/types"
	"math/big"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// twoRules returns the typed rules of a generic.rules file of two rules.
func twoRules(t *testing.T, text string) (*typecheck.Result, [2]*rules.Rule) {
	t.Helper()
	c := rules.Parse(analysistest.Tables(t), map[string][]byte{"generic.rules": []byte(text)})
	for _, err := range c.Errors {
		t.Fatal(err)
	}
	set := c.Sets[0]
	res, err := typecheck.Check(set)
	if err != nil {
		t.Fatal(err)
	}
	return res, [2]*rules.Rule{set.Rules[0], set.Rules[1]}
}

// constAux returns the identifier that binds the auxint of the rule's
// match's second argument.
func constAux(res *typecheck.Result, r *rules.Rule) ast.Expr {
	return res.Rule(r).Expr(r.Match.Args[1], typecheck.AuxInt)
}

func TestAssumeNot(t *testing.T) {
	res, rs := twoRules(t, `
(Lsh64x64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])
(Lsh64x64 x (Const64 [e])) && x.Uses == 1 => (Const64 [e])
`)
	f := facts.New(res, rs[1])
	e := constAux(res, rs[1])
	c := res.Rule(rs[0]).Vars["c"]
	g := f.AssumeNot(res.Rule(rs[0]).Cond, map[types.Object]ast.Expr{c: e})
	if r, _ := g.Range(e); r.String() != "[0, 63]" {
		t.Errorf("Range(e) = %v, want [0, 63]", r)
	}
	if r, _ := f.Range(e); r.String() != "[-9223372036854775808, 9223372036854775807]" {
		t.Errorf("without AssumeNot, Range(e) = %v", r)
	}
	vals := func(x int64) map[types.Object]any {
		return map[types.Object]any{res.Rule(rs[1]).Vars["e"]: big.NewInt(x)}
	}
	// x.Uses == 1 does not depend on e, so it may hold.
	if !g.Holds(vals(5)) {
		t.Errorf("Holds(e=5) = false, want true")
	}
	if g.Holds(vals(64)) || g.Holds(vals(-1)) {
		t.Errorf("Holds(e=64 or -1) = true, want false: the earlier rule fires")
	}
}

func TestAssumeInExcludeVar(t *testing.T) {
	res, rs := twoRules(t, `
(Lsh64x64 (Rsh64Ux64 x (Const64 [c])) (Const64 [64-c])) && c >= 0 && c < 100 => (Const64 [c])
(Rsh64x64 x (Const64 [c])) && uint32(c) < 32 => (Const32 [int32(c)])
`)
	f := facts.New(res, rs[0])
	in := f.AssumeIn(constAux(res, rs[0]), facts.Range(0, 63))
	e := res.Rule(rs[0]).Expr(rs[0].Result, typecheck.AuxInt)
	if r, _ := in.Range(e); r.String() != "[1, 64]" {
		t.Errorf("Range(c) = %v, want [1, 64]", r)
	}
	ex := in.ExcludeVar("c", big.NewInt(64))
	if r, _ := ex.Range(e); r.String() != "[1, 63]" {
		t.Errorf("Range(c) = %v, want [1, 63]", r)
	}
	c := res.Rule(rs[0]).Vars["c"]
	if ex.Holds(map[types.Object]any{c: big.NewInt(64)}) || !ex.Holds(map[types.Object]any{c: big.NewInt(63)}) {
		t.Errorf("Holds disagrees with AssumeIn and ExcludeVar")
	}

	// Eval follows Go semantics.
	f = facts.New(res, rs[1])
	e = res.Rule(rs[1]).Expr(rs[1].Result, typecheck.AuxInt)
	c = res.Rule(rs[1]).Vars["c"]
	v, ok := f.Eval(e, map[types.Object]any{c: big.NewInt(1<<32 + 5)})
	if !ok || v.(*big.Int).Int64() != 5 {
		t.Errorf("Eval(int32(c)) = %v, %v, want 5", v, ok)
	}
	// So does the condition: uint32(c) < 32.
	if !f.Holds(map[types.Object]any{c: big.NewInt(1<<32 + 5)}) || f.Holds(map[types.Object]any{c: big.NewInt(32)}) {
		t.Errorf("Holds disagrees with the condition")
	}
}
