package facts_test

import (
	"go/ast"
	"go/types"
	"strings"
	"sync"
	"testing"

	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var tip struct {
	once   sync.Once
	corpus *rules.Corpus
	err    error
}

func loadTip(t *testing.T) *rules.Corpus {
	t.Helper()
	root := testenv.GoRoot(t)
	tip.once.Do(func() { tip.corpus, tip.err = rules.Load(root) })
	if tip.err != nil {
		t.Fatal(tip.err)
	}
	return tip.corpus
}

// subject is a rule under test.
type subject struct {
	t    *testing.T
	rule *rules.Rule
	tr   *typecheck.Rule
	f    *facts.Facts
}

func newSubject(t *testing.T, set *rules.RuleSet, r *rules.Rule) *subject {
	t.Helper()
	res, err := typecheck.Check(set)
	if err != nil {
		t.Fatal(err)
	}
	tr := res.Rule(r)
	for _, err := range tr.Errors {
		t.Fatalf("%s: %v", r.Pos, err)
	}
	return &subject{t: t, rule: r, tr: tr, f: facts.New(res, r)}
}

// tipRule returns the first rule of the Go tree's rule set whose text
// contains each of substrs.
func tipRule(t *testing.T, set string, substrs ...string) *subject {
	t.Helper()
	for _, s := range loadTip(t).Sets {
		if s.Name() != set {
			continue
		}
	rules:
		for _, r := range s.Rules {
			for _, sub := range substrs {
				if !strings.Contains(r.Text, sub) {
					continue rules
				}
			}
			return newSubject(t, s, r)
		}
	}
	t.Skipf("no %s rule containing %q in this tree", set, substrs)
	return nil
}

// fixture returns the rule of a generic.rules file containing just text.
func fixture(t *testing.T, text string) *subject {
	t.Helper()
	c := rules.Parse(analysistest.Tables(t), map[string][]byte{"generic.rules": []byte(text + "\n")})
	for _, err := range c.Errors {
		t.Fatal(err)
	}
	set := c.Sets[0]
	return newSubject(t, set, set.Rules[0])
}

// result returns the [auxint] of the rule's result.
func (s *subject) result() ast.Expr {
	s.t.Helper()
	var e ast.Expr
	if s.rule.IsBlock() {
		e = s.tr.Expr(s.rule.ResultBlock.Controls[0], typecheck.AuxInt)
	} else {
		e = s.tr.Expr(s.rule.Result, typecheck.AuxInt)
	}
	if e == nil {
		s.t.Fatalf("%s: no result auxint", s.rule.Pos)
	}
	return e
}

// expr returns the sub-expression of the rule's condition or result
// auxints that prints as text.
func (s *subject) expr(text string) ast.Expr {
	s.t.Helper()
	roots := []ast.Expr{s.tr.Cond}
	for _, v := range s.rule.ResultValues() {
		v.Walk(func(v *rules.Value) bool {
			roots = append(roots, s.tr.Expr(v, typecheck.AuxInt))
			return true
		})
	}
	var found ast.Expr
	for _, root := range roots {
		if root == nil {
			continue
		}
		ast.Inspect(root, func(n ast.Node) bool {
			if e, ok := n.(ast.Expr); ok && found == nil && types.ExprString(e) == text {
				found = e
			}
			return found == nil
		})
	}
	if found == nil {
		s.t.Fatalf("%s: no expression %s in %s", s.rule.Pos, text, s.rule.Text)
	}
	return found
}

func (s *subject) wantRange(e ast.Expr, want string) {
	s.t.Helper()
	r, ok := s.f.Range(e)
	if !ok {
		s.t.Errorf("%s: Range(%s) not ok", s.rule.Pos, types.ExprString(e))
		return
	}
	if r.String() != want {
		s.t.Errorf("%s: Range(%s) = %v, want %s\n\t%s", s.rule.Pos, types.ExprString(e), r, want, s.rule.Text)
	}
}

func (s *subject) wantExact(e ast.Expr, want bool) {
	s.t.Helper()
	if got := s.f.Exact(e); got != want {
		s.t.Errorf("%s: Exact(%s) = %v, want %v (overflows %v)\n\t%s", s.rule.Pos, types.ExprString(e), got, want, fmtOverflows(s.f.Overflows(e)), s.rule.Text)
	}
}

func (s *subject) wantOverflows(os []facts.Overflow, want string) {
	s.t.Helper()
	if got := fmtOverflows(os); got != want {
		s.t.Errorf("%s: overflows %s, want %s\n\t%s", s.rule.Pos, got, want, s.rule.Text)
	}
}

func fmtOverflows(os []facts.Overflow) string {
	var s []string
	for _, o := range os {
		s = append(s, types.ExprString(o.Expr)+" "+o.Type.String()+" "+o.Range.String())
	}
	return strings.Join(s, "; ")
}

// Tests on rules of the Go tree.

func TestOffsetSum(t *testing.T) {
	// The sum of two int32 offsets, proven to fit by is32Bit,
	// which is inlined from its definition.
	s := tipRule(t, "AMD64", "(ADDQconst [c] (ADDQconst [d] x)) && ssa.Is32Bit(int64(c)+int64(d))")
	s.wantExact(s.result(), true)
	s.wantRange(s.expr("int64(c) + int64(d)"), "[-2147483648, 2147483647]")
}

func TestScaledOffset(t *testing.T) {
	// c+2*d is exact even though 2*d may wrap, since + and *
	// are exact modulo 2^32.
	s := tipRule(t, "AMD64", "(LEAQ2 [c] {s} x (ADDQconst [d] y)) && ssa.Is32Bit(int64(c)+2*int64(d))")
	s.wantExact(s.result(), true)
}

func TestModularOffset(t *testing.T) {
	// scale is a 64-bit constant; int32(scale) truncates it. The int32
	// result is not its mathematical value, but it is right modulo
	// 2^64, which is what the 64-bit LEAQ needs.
	s := tipRule(t, "AMD64", "(LEAQ2 [off] {sym} x (MOVQconst [scale])) && ssa.Is32Bit(int64(off)+int64(scale)*2)")
	e := s.result()
	s.wantExact(e, false)
	s.wantOverflows(s.f.Overflows(e), "off + int32(scale) * 2 int32 [-18446744075857035264, 18446744075857035261]")
	s.wantOverflows(s.f.OverflowsMod(e, 64), "")
	s.wantOverflows(s.f.OverflowsMod(s.expr("int32(scale)"), 64), "int32(scale) int32 [-9223372036854775808, 9223372036854775807]")
}

func TestNegate(t *testing.T) {
	// -c is exact if c is not the most negative int32.
	s := tipRule(t, "AMD64", "(SUBQconst [c] x) && c != -(1<<31)")
	s.wantExact(s.result(), true)
	s.wantRange(s.expr("c"), "[-2147483647, 2147483647]")

	// Without that condition, -c wraps, but the 32-bit ADDLconst
	// needs it only modulo 2^32.
	s = tipRule(t, "AMD64", "(SUBLconst [c] x) => (ADDLconst [-c] x)")
	s.wantOverflows(s.f.Overflows(s.result()), "-c int32 [-2147483647, 2147483648]")
	s.wantOverflows(s.f.OverflowsMod(s.result(), 32), "")
	s.wantOverflows(s.f.OverflowsMod(s.result(), 64), "-c int32 [-2147483647, 2147483648]")
}

func TestLog(t *testing.T) {
	// isPowerOfTwo(n) means n > 0, so log64u of it is in [0, 63].
	s := tipRule(t, "generic", "(Div64u n (Const64 [c])) && ssa.IsPowerOfTwo(uint64(c))")
	e := s.expr("ssa.Log64u(uint64(c))")
	s.wantRange(e, "[0, 63]")
	s.wantExact(e, true)

	// uint64(c) ≥ 1<<31 bounds the log from below.
	s = tipRule(t, "AMD64", "(ORQ (MOVQconst [c]) x) && ssa.IsPowerOfTwo(uint64(c)) && uint64(c) >= 1<<31")
	s.wantRange(s.result(), "[31, 63]")
	s.wantRange(s.expr("uint64(c)"), "[2147483648, 18446744073709551615]")

	// In int8, -c wraps for c = -128, making uint8(-c) 128, whose log is 7.
	s = tipRule(t, "generic", "(Mul8 <t> x (Const8 [c])) && ssa.IsPowerOfTwo(uint8(-c))")
	s.wantRange(s.expr("ssa.Log8u(uint8(-c))"), "[0, 7]")

	// int16(c) may be 0 or negative even if c is a positive int32,
	// so log16 of it may be -1, and uint8 of that, 255.
	s = tipRule(t, "AMD64", "(VPMULLW128 x (VPBROADCASTW128 (VMOVQ (MOVLconst [c])))) && ssa.IsPowerOfTwo(c)")
	s.wantRange(s.expr("ssa.Log16(int16(c))"), "[-1, 15]")
	s.wantRange(s.result(), "[0, 255]")
}

func TestTrailingZeros(t *testing.T) {
	// ntz32(c) is bits.TrailingZeros32(uint32(c)): 32 if c is 0.
	s := tipRule(t, "generic", "(Ctz32 (Const32 [c])) && config.PtrSize == 8")
	s.wantRange(s.result(), "[0, 32]")
	s.wantRange(s.expr("config.PtrSize"), "[8]")
}

func TestTruncation(t *testing.T) {
	// Nothing bounds c: int8(c) may truncate.
	s := tipRule(t, "AMD64", "(CMPB x (MOVLconst [c])) => (CMPBconst x [int8(c)])")
	c := s.expr("c")
	if s.f.Fits(c, types.Typ[types.Int8]) {
		t.Errorf("Fits(c, int8) = true, want false")
	}
	if !s.f.Fits(c, types.Typ[types.Int64]) {
		t.Errorf("Fits(c, int64) = false, want true")
	}
	s.wantOverflows(s.f.Overflows(s.result()), "int8(c) int8 [-2147483648, 2147483647]")
}

func TestUnsignedImmediate(t *testing.T) {
	// y is in [256, 2^32-1], so int32(y) may be negative. (!isU8Bit
	// excludes [0, 255], which an interval cannot express.)
	s := tipRule(t, "S390X", "(CLGRJ {c} x (MOVDconst [y]) yes no) && !isU8Bit(y) && ssa.IsU32Bit(y)")
	s.wantRange(s.expr("y"), "[0, 4294967295]")
	if s.f.Fits(s.expr("y"), types.Typ[types.Int32]) {
		t.Errorf("Fits(y, int32) = true, want false")
	}
	s.wantRange(s.result(), "[-2147483648, 2147483647]")

	s = tipRule(t, "S390X", "(CL(R|GR)J {c} x (MOVDconst [y]) yes no) && isU8Bit(y)")
	s.wantRange(s.expr("y"), "[0, 255]")
	s.wantExact(s.expr("uint8(y)"), true)
}

func TestWrappedCondition(t *testing.T) {
	// isU32Bit(off+off2) bounds off+off2's Go value, which may have
	// wrapped around: off and off2 may be huge.
	s := tipRule(t, "Wasm", "(I64Store32 [off] (I64AddConst [off2] ptr) val mem) && ssa.IsU32Bit(off+off2)")
	e := s.result()
	s.wantRange(e, "[0, 4294967295]")
	s.wantExact(e, false)
	s.wantOverflows(s.f.OverflowsMod(e, 64), "")
	s.wantRange(s.expr("off"), "[-9223372036854775808, 9223372036854775807]")
}

func TestDivide(t *testing.T) {
	s := tipRule(t, "generic", "(Div8 (Const8 [c]) (Const8 [d])) && d != 0")
	if !s.f.NonZero(s.expr("d")) {
		t.Errorf("NonZero(d) = false, want true")
	}
	if s.f.NonZero(s.expr("c")) {
		t.Errorf("NonZero(c) = true, want false")
	}
	// -128 / -1 overflows int8.
	s.wantOverflows(s.f.Overflows(s.result()), "c / d int8 [-128, 128]")
}

func TestMin(t *testing.T) {
	s := tipRule(t, "AMD64", "(SARB x (MOVQconst [c])) => (SARBconst [int8(min(int64(c)&31,7))] x)")
	s.wantRange(s.result(), "[0, 7]")
	s.wantExact(s.result(), true)
}

func TestAssumeVar(t *testing.T) {
	// c and d are bit indexes, though their type, int8, does not say so.
	s := tipRule(t, "AMD64", "(BTQconst [c] (SHRQconst [d] x)) && (c+d)<64")
	e := s.result()
	s.wantRange(e, "[-128, 63]")
	s.wantExact(e, false)
	s.f = s.f.AssumeVar("c", facts.Range(0, 63)).AssumeVar("d", facts.Range(0, 63))
	s.wantRange(e, "[0, 63]")
	s.wantExact(e, true)
}

func TestValAndOff(t *testing.T) {
	// Methods of ValAndOff and MakeValAndOff are inlined.
	s := tipRule(t, "AMD64", "(MOVQstoreconst [c] {s} p1 x:(MOVQstoreconst [a] {s} p0 mem))", "a.Val() == 0")
	s.wantRange(s.expr("a.Val()"), "[0]")
	s.wantRange(s.expr("a.Off()"), "[-2147483648, 2147483647]")
	s.wantRange(s.result(), "[0, 4294967295]")
}

// Tests on synthetic rules, for constructs the Go tree may lack.

func TestFixtures(t *testing.T) {
	tests := []struct {
		rule string
		expr string // in the condition or result auxint
		want string // its range
	}{
		// Comparisons, in either order.
		{"(Const64 [c]) && c > 3 && 10 >= c => (Const64 [c])", "c", "[4, 10]"},
		{"(Const64 [c]) && !(c < 3) && !(c >= 10) => (Const64 [c])", "c", "[3, 9]"},
		// Facts common to both sides of ||.
		{"(Const64 [c]) && (c == 1 || c == 3) => (Const64 [c])", "c", "[1, 3]"},
		{"(Const64 [c]) && (c == 1 || c > 0 && c < 5) => (Const64 [c])", "c", "[1, 4]"},
		{"(Add64 (Const64 [c]) (Const64 [d])) && (c == 1 || d == 3) => (Const64 [c])", "c", "[-9223372036854775808, 9223372036854775807]"},
		// The right side of || is evaluated only if the left is false.
		{"(Const64 [c]) && c >= 0 && (c > 5 || c == 0) && c < 9 => (Const64 [c])", "c", "[0, 8]"},
		// != narrows an end.
		{"(Const64 [c]) && c >= 0 && c != 0 => (Const64 [c])", "c", "[1, 9223372036854775807]"},
		// Comparisons between variables.
		{"(Add64 (Const64 [c]) (Const64 [d])) && 0 <= c && c < d && d < 10 => (Const64 [d-c])", "c", "[0, 8]"},
		{"(Add64 (Const64 [c]) (Const64 [d])) && 0 <= c && c < d && d < 10 => (Const64 [d-c])", "d", "[1, 9]"},
		// A comparison of variables bounds their difference.
		{"(Add64 (Const64 [c]) (Const64 [d])) && 0 <= c && c < d && d < 10 => (Const64 [d-c])", "d - c", "[1, 9]"},
		{"(Add64 (Const64 [c]) (Const64 [d])) && 0 <= c && c < d && d < 10 => (Const64 [c-d])", "c - d", "[-9, -1]"},
		{"(Add32 (Const32 [c]) (Const32 [d])) && c >= d => (Const64 [int64(c)-int64(d)])", "int64(c) - int64(d)", "[0, 4294967295]"},
		// But only exact differences: c-d may wrap.
		{"(Add64 (Const64 [c]) (Const64 [d])) && c > d => (Const64 [c-d])", "c - d", "[-9223372036854775808, 9223372036854775807]"},
		// uint64(c) > 0 excludes c == 0, which int32-to-uint32 preserves.
		{"(Const32 [c]) && uint64(c) > 0 => (Const32 [int32(uint32(c))])", "uint32(c)", "[1, 4294967295]"},
		// Ring facts carry through sums.
		{"(Const64 [c]) && uint32(c) < 16 => (Const32 [int32(c+16)])", "int32(c + 16)", "[16, 31]"},
		// A ring fact holds for both signednesses.
		{"(Const64 [c]) && uint32(c) < 32 => (Const32 [int32(c)])", "int32(c)", "[0, 31]"},
		// Conversions: uint64(c) < 64 means 0 ≤ c < 64.
		{"(Const64 [c]) && uint64(c) < 64 => (Const64 [c])", "c", "[0, 63]"},
		{"(Const8 [c]) && uint32(c) >= 1 && uint32(c) <= 100 => (Const8 [c])", "c", "[1, 100]"},
		// A narrowing conversion says nothing about its operand.
		{"(Const64 [c]) && int8(c) == 3 => (Const64 [c])", "c", "[-9223372036854775808, 9223372036854775807]"},
		// Masks, remainders, shifts.
		{"(Const64 [c]) => (Const64 [c & 0xff])", "c & 0xff", "[0, 255]"},
		{"(Const64 [c]) => (Const64 [c % 8])", "c % 8", "[-7, 7]"},
		{"(Const64 [c]) && c >= 0 => (Const64 [c % 8])", "c % 8", "[0, 7]"},
		{"(Const64 [c]) => (Const64 [int64(uint64(c) >> 60)])", "int64(uint64(c) >> 60)", "[0, 15]"},
		{"(Const64 [c]) => (Const64 [c >> 60])", "c >> 60", "[-8, 7]"},
		{"(Const64 [c]) && c >= 0 && c < 4 => (Const64 [1 << uint(c)])", "1 << uint(c)", "[1, 8]"},
		{"(Add32 (Const32 [c]) (Const32 [d])) && c >= -4 && c < 3 && d >= -2 && d < 1 => (Const32 [c & d])", "c & d", "[-4, 3]"},
		// Math facts transfer between expressions with the same
		// mathematical value: int64(c)+1 fits, so c+1 does.
		{"(Const32 [c]) && int64(c)+1 < 100 && c >= 0 => (Const32 [c+1])", "c + 1", "[1, 99]"},
		{"(Const32 [c]) && int64(c)+1 < 100 && c >= 0 => (Const32 [c+1])", "c", "[0, 98]"},
	}
	for _, tt := range tests {
		t.Run(tt.rule, func(t *testing.T) {
			s := fixture(t, tt.rule)
			s.wantRange(s.expr(tt.expr), tt.want)
		})
	}
}

func TestContradiction(t *testing.T) {
	// The rule never fires, so anything holds.
	s := fixture(t, "(Const64 [c]) && c > 3 && c < 2 => (Const64 [c])")
	if !s.f.In(s.result(), 100, 100) {
		t.Errorf("In(c, 100, 100) = false, want true")
	}
}

func TestNotInteger(t *testing.T) {
	s := fixture(t, "(Const64 [c]) && c > 3 => (Const64 [c])")
	if _, ok := s.f.Range(s.tr.Cond); ok {
		t.Errorf("Range(cond) ok")
	}
	if s.f.In(s.tr.Cond, 0, 1) || s.f.NonZero(s.tr.Cond) || s.f.Fits(s.tr.Cond, types.Typ[types.Int64]) {
		t.Errorf("query on a boolean answered true")
	}
}

// TestAll runs every query on every expression of every rule of the
// Go tree, which must not panic.
func TestAll(t *testing.T) {
	c := loadTip(t)
	n := 0
	for _, set := range c.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			t.Fatal(err)
		}
		for _, r := range set.Rules {
			f := facts.New(res, r)
			tr := res.Rule(r)
			var roots []ast.Expr
			for _, v := range r.ResultValues() {
				v.Walk(func(v *rules.Value) bool {
					if e := tr.Expr(v, typecheck.AuxInt); e != nil {
						roots = append(roots, e)
					}
					return true
				})
			}
			if tr.Cond != nil {
				roots = append(roots, tr.Cond)
			}
			for _, root := range roots {
				ast.Inspect(root, func(nd ast.Node) bool {
					if e, ok := nd.(ast.Expr); ok {
						n++
						f.Range(e)
						f.NonZero(e)
						f.Overflows(e)
						f.OverflowsMod(e, 32)
					}
					return true
				})
			}
		}
	}
	t.Logf("%d expressions", n)
}

func TestHistorical(t *testing.T) {
	if testing.Short() {
		t.Skip("slow")
	}
	// In older trees, helpers like is32Bit are in package ssa, along
	// with the generated rewrite code.
	dir, err := gitrev.GenDir(testenv.GoRepo(t), "go1.22.0")
	if err != nil {
		t.Fatal(err)
	}
	c, err := rules.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, set := range c.Sets {
		if set.Name() != "AMD64" {
			continue
		}
		for _, r := range set.Rules {
			if strings.Contains(r.Text, "(ADDQconst [c] (ADDQconst [d] x)) && is32Bit(int64(c)+int64(d))") {
				s := newSubject(t, set, r)
				s.wantExact(s.result(), true)
				return
			}
		}
	}
	t.Fatal("rule not found")
}

func TestNonZero(t *testing.T) {
	for _, rule := range []string{
		"(Const64 [c]) && c != 0 => (Const64 [c])",
		"(Const64 [c]) && uint64(c) != 0 => (Const64 [c])",
		"(Const64 [c]) && !(c == 0) => (Const64 [c])",
		"(Const64 [c]) && ssa.OneBit(c) => (Const64 [c])",
		"(Const64 [c]) && ssa.IsPowerOfTwo(c) => (Const64 [c])",
	} {
		s := fixture(t, rule)
		if !s.f.NonZero(s.result()) {
			t.Errorf("%s: NonZero(c) = false, want true", rule)
		}
	}
	for _, rule := range []string{
		"(Const64 [c]) => (Const64 [c])",
		"(Const64 [c]) && (c != 0 || c == 0) => (Const64 [c])",
	} {
		s := fixture(t, rule)
		if s.f.NonZero(s.result()) {
			t.Errorf("%s: NonZero(c) = true, want false", rule)
		}
	}
}

func TestConstantReturns(t *testing.T) {
	// MoveSize returns 8, 4, 2, or 1 from a switch, so it is not
	// inlined, but it is bounded by those constants.
	s := tipRule(t, "MIPS64", "(Zero [s] {t} ptr mem)", "LoweredZero")
	s.wantRange(s.expr("ssa.MoveSize(t.Alignment(), config)"), "[1, 8]")
}

func TestAt(t *testing.T) {
	// The guard protects c%d only if it is evaluated first.
	for _, tc := range []struct {
		cond string
		want bool
	}{
		{"d != 0 && c%d == 0", true},
		{"c%d == 0 && d != 0", false},
		{"d == 0 || c%d == 0", true},
		{"d > 0 && (d == 1 || c%d == 0)", true},
	} {
		s := fixture(t, "(Div64 (Const64 [c]) (Const64 [d])) && "+tc.cond+" => (Const64 [c])")
		res, err := typecheck.Check(s.rule.Set)
		if err != nil {
			t.Fatal(err)
		}
		d := s.expr("c % d").(*ast.BinaryExpr).Y
		if got := facts.At(res, s.rule, d).NonZero(d); got != tc.want {
			t.Errorf("%s: NonZero(d) at c%%d = %v, want %v", tc.cond, got, tc.want)
		}
	}
}
