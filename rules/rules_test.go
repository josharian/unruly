package rules_test

import (
	"slices"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

func tables(t *testing.T) *ops.Tables {
	t.Helper()
	tab, err := ops.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	return tab
}

// parse parses src as the named rules file and returns its rules,
// failing the test on errors.
func parse(t *testing.T, name, src string) []*rules.Rule {
	t.Helper()
	c := rules.Parse(tables(t), map[string][]byte{name: []byte(src)})
	for _, err := range c.Errors {
		t.Fatal(err)
	}
	if len(c.Sets) != 1 {
		t.Fatalf("got %d rule sets, want 1", len(c.Sets))
	}
	return c.Sets[0].Rules
}

func TestValueRuleShape(t *testing.T) {
	rs := parse(t, "generic.rules", `
// A comment.
(Add(64|32) <t> x
    y:(Const(64|32) [0]))  // trailing comment
  && x.Type.IsInteger()
  => x
`)
	if len(rs) != 2 {
		t.Fatalf("got %d rules, want 2", len(rs))
	}
	r := rs[1]
	if r.Pos.Line != 3 || r.EndLine != 6 || r.Alt != 1 || r.NumAlts != 2 {
		t.Errorf("pos %v end %d alt %d/%d", r.Pos, r.EndLine, r.Alt, r.NumAlts)
	}
	if want := "(Add(64|32) <t> x y:(Const(64|32) [0])) && x.Type.IsInteger() => x"; r.Orig != want {
		t.Errorf("Orig = %q, want %q", r.Orig, want)
	}
	if r.MatchText != "(Add32 <t> x y:(Const32 [0]))" || r.Cond != "x.Type.IsInteger()" || r.ResultText != "x" {
		t.Errorf("parts = %q, %q, %q", r.MatchText, r.Cond, r.ResultText)
	}
	if r.CondExpr == nil {
		t.Error("CondExpr is nil")
	}
	m := r.Match
	if m.Op.QualifiedName() != "Add32" || !m.Op.IsGeneric() || m.Type != "t" || len(m.Args) != 2 || !m.Commutes() {
		t.Errorf("match = %+v", m)
	}
	if x := m.Args[0]; !x.IsLeaf() || !x.IsVar() || x.Name != "x" {
		t.Errorf("arg 0 = %+v", x)
	}
	if y := m.Args[1]; y.Name != "y" || y.OpName != "Const32" || y.AuxInt != "0" || y.Text != "(Const32 [0])" {
		t.Errorf("arg 1 = %+v", y)
	}
	if res := r.Result; !res.IsLeaf() || res.Name != "x" {
		t.Errorf("result = %+v", res)
	}
}

func TestResultForms(t *testing.T) {
	rs := parse(t, "AMD64.rules", `
(MOVQload [off] {sym} ptr mem) && false => @mem.Block (MOVQload [off] {sym} ptr mem)
(MULQconst [c] x) && c == 7 => {mulBy7(v, x)}
(ADDQ x (MOVQconst [c])) && is32Bit(c) => (ADDQconst [int32(c)] x)
(CMPQ x y) && false => (InvertFlags (CMPQ <types.TypeFlags> y x))
`)
	r := rs[0]
	if r.Placement != "mem.Block" || r.Result.OpName != "MOVQload" {
		t.Errorf("placement %q result %v", r.Placement, r.Result)
	}
	if typ, src := r.ResultType(r.Result); src != rules.TypeOpDefault || typ != "UInt64" {
		t.Errorf("@block result type = %q, %v", typ, src)
	}
	if r := rs[1]; r.ResultCode != "mulBy7(v, x)" || r.Result != nil {
		t.Errorf("code result %q %v", r.ResultCode, r.Result)
	}
	if r := rs[2]; r.Result.Op.Arch.Name != "AMD64" || r.Result.AuxInt != "int32(c)" {
		t.Errorf("result %+v", r.Result)
	}
	if _, src := rs[2].ResultType(rs[2].Result); src != rules.TypeInherited {
		t.Errorf("top-level result type source = %v", src)
	}
	inner := rs[3].Result.Args[0]
	if typ, src := rs[3].ResultType(inner); src != rules.TypeExplicit || typ != "types.TypeFlags" {
		t.Errorf("inner result type = %q, %v", typ, src)
	}
	if _, src := rs[3].ResultType(inner.Args[0]); src != rules.TypeExisting {
		t.Errorf("leaf result type source = %v", src)
	}
}

func TestBlockRule(t *testing.T) {
	rs := parse(t, "generic.rules", `
(If (ConstBool [c]) yes no) && c => (First yes no)
(If (Not cond) yes no) => (If cond no yes)
`)
	r := rs[0]
	if !r.IsBlock() || r.Match != nil {
		t.Fatal("not a block rule")
	}
	mb, rb := r.MatchBlock, r.ResultBlock
	if mb.Info.Name != "If" || len(mb.Controls) != 1 || mb.Controls[0].AuxInt != "c" || !slices.Equal(mb.Succs, []string{"yes", "no"}) {
		t.Errorf("match block %+v", mb)
	}
	if rb.Info.Name != "First" || len(rb.Controls) != 0 || !slices.Equal(rb.Succs, []string{"yes", "no"}) {
		t.Errorf("result block %+v", rb)
	}
	if rb := rs[1].ResultBlock; !slices.Equal(rb.Succs, []string{"no", "yes"}) || rb.Controls[0].Name != "cond" {
		t.Errorf("swapped block %+v", rb)
	}
	set := r.Set
	if got := set.ByBlock[mb.Info]; len(got) != 2 {
		t.Errorf("ByBlock has %d rules", len(got))
	}
}

func TestEllipsisAndRest(t *testing.T) {
	rs := parse(t, "AMD64.rules", `
(Add64 ...) => (ADDQ ...)
(Last ___) => v.Args[len(v.Args)-1]
(StructMake x ___) && false => x
`)
	if r := rs[0]; !r.Match.Ellipsis || !r.Result.Ellipsis || len(r.Match.Args) != 0 || !r.Unconditional() {
		t.Errorf("ellipsis rule %+v", r.Match)
	}
	if r := rs[1]; !r.Match.Rest || len(r.Match.Args) != 0 || r.Result.Name != "v.Args[len(v.Args)-1]" || !r.Unconditional() {
		t.Errorf("rest rule %+v %+v", r.Match, r.Result)
	}
	if r := rs[2]; !r.Match.Rest || len(r.Match.Args) != 1 {
		t.Errorf("rest rule %+v", r.Match)
	}
}

func TestMatchVars(t *testing.T) {
	rs := parse(t, "generic.rules", `
(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) => x
(Sub64 x x) => (Const64 [0])
(Eq64 (Const64 <t> [0]) x:(Neg64 x)) => (ConstBool [false])
`)
	vars := rs[0].MatchVars()
	var names []string
	for n := range vars {
		names = append(names, n)
	}
	slices.Sort(names)
	if !slices.Equal(names, []string{"p1", "p2", "t1", "t2", "x"}) {
		t.Errorf("vars = %v", names)
	}
	if o := vars["t2"]; len(o) != 1 || o[0].Kind != rules.OccAux || o[0].Value.OpName != "Store" {
		t.Errorf("t2 = %+v", o)
	}
	if o := rs[1].MatchVars()["x"]; len(o) != 2 {
		t.Errorf("x in (Sub64 x x) occurs %d times", len(o))
	}
	// A name can be bound by x:(...) and then compared as a leaf.
	if o := rs[2].MatchVars()["x"]; len(o) != 2 || o[0].Value.OpName != "Neg64" || !o[1].Value.IsLeaf() {
		t.Errorf("x = %+v", o)
	}
	if _, ok := rs[2].MatchVars()["t"]; !ok {
		t.Errorf("t missing")
	}
}

func TestCommutations(t *testing.T) {
	rs := parse(t, "generic.rules", `(Sub64 (Add64 (Mul64 x y) z) w) => w`)
	var got []string
	for _, v := range rules.Commutations(rs[0].Match) {
		got = append(got, format(v))
	}
	want := []string{
		"(Sub64 (Add64 (Mul64 x y) z) w)",
		"(Sub64 (Add64 (Mul64 y x) z) w)",
		"(Sub64 (Add64 z (Mul64 x y)) w)",
		"(Sub64 (Add64 z (Mul64 y x)) w)",
	}
	if !slices.Equal(got, want) {
		t.Errorf("got\n%s\nwant\n%s", strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
}

func format(v *rules.Value) string {
	if v.IsLeaf() {
		return v.Name
	}
	s := "(" + v.OpName
	for _, a := range v.Args {
		s += " " + format(a)
	}
	return s + ")"
}

func TestUnconditional(t *testing.T) {
	for _, tt := range []struct {
		rule string
		want bool
	}{
		{"(Neg64 x) => (Sub64 (Const64 <v.Type> [0]) x)", true},
		{"(Load <t> ptr mem) => (Load <t> mem ptr)", true},
		{"(Sub64 x x) => (Const64 [0])", false},
		{"(Neg64 (Neg64 x)) => x", false},
		{"(Neg64 x) && false => x", false},
		{"(Const64 [0]) => (Const64 [1])", false},
		{"(Load <typ.UInt64> ptr mem) => (Load <t> mem ptr)", false},
		{"(StructMake ___) => (StructMake)", true},
		{"(StructMake x) => (StructMake)", false},
		{"(If cond yes no) => (If cond no yes)", true},
		{"(If (Not cond) yes no) => (If cond no yes)", false},
	} {
		rs := parse(t, "generic.rules", tt.rule)
		if got := rs[0].Unconditional(); got != tt.want {
			t.Errorf("%s: Unconditional() = %v, want %v", tt.rule, got, tt.want)
		}
	}
}

func TestErrors(t *testing.T) {
	tab := tables(t)
	for _, tt := range []struct {
		name, src, err string
	}{
		{"generic.rules", "(Frob x) => x", "unknown op Frob"},
		{"generic.rules", "(Add64 x) => x", "should have 2 args, has 1"},
		{"generic.rules", "(Add64 [c] x y) => x", "can't have auxint"},
		{"generic.rules", "(Neg64 x) => (Neg64 (Neg64 x))", "must have a type"},
		{"generic.rules", "(Add64 x ___) => x", "not variadic"},
		{"generic.rules", "(Add64 ... x) => x", "... must be the only argument"},
		{"generic.rules", "(Add64 ...) && true => (Add32 ...)", "ellipsis in non-ellipsis rule"},
		{"generic.rules", "(If cond yes no) => (If cond yes yes)", "can't have a repeat successor|unknown successor|unmatched"},
		{"generic.rules", "(Neg64 x\n", "unbalanced rule"},
		{"generic.rules", "(Neg64 x)\n", "incomplete rule"},
		{"generic.rules", "(Neg64 x) -> x\n", "untyped"},
		{"generic.rules", "(Neg64 v) => v", "reserved name v"},
		{"generic.rules", "(Neg64 x) => x\n(Neg64 y) && y != nil => y", "follows unconditional rule"},
		{"generic.rules", "(Add64 x y) && x + => x", "failed to parse cond"},
		{"generic.rules", "(Add(64|32) (Const(64|32|16) x)) => x", "count doesn't match"},
		{"AMD64.rules", "(Neg64 (Neg64 <t> x)) => (Neg64 (Neg64 <t> x))\n(FOO x) => x", "unknown op FOO"},
		{"bogus.rules", "(Neg64 x) => x", "does not belong to any arch"},
	} {
		c := rules.Parse(tab, map[string][]byte{tt.name: []byte(tt.src)})
		var msgs []string
		for _, e := range c.Errors {
			msgs = append(msgs, e.Error())
		}
		joined := strings.Join(msgs, "\n")
		if !regexpMatch(tt.err, joined) {
			t.Errorf("%q: errors %q, want match for %q", tt.src, joined, tt.err)
		}
	}
}

func regexpMatch(pattern, s string) bool {
	for _, p := range strings.Split(pattern, "|") {
		if strings.Contains(s, p) {
			return true
		}
	}
	return false
}

func TestSetFiles(t *testing.T) {
	if got := rules.SetFiles("ARM64", ""); !slices.Equal(got, []string{"ARM64.rules", "simdARM64.rules", "simdARM64SVE.rules"}) {
		t.Errorf("SetFiles(ARM64) = %v", got)
	}
	rs := parse(t, "AMD64latelower.rules", "(SHLQ x y) && false => (SHLXQ x y)")
	if s := rs[0].Set; s.Name() != "AMD64latelower" || s.Suffix != "latelower" || s.Arch.Name != "AMD64" {
		t.Errorf("set %v", s)
	}
}
