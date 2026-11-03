// Package auxdomain reports rules that create an auxint outside the range
// its op accepts.
package auxdomain

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"math/big"
	"math/bits"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/auxdomain/prior"
	"github.com/josharian/unruly/analyzers/auxdomain/witness"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "auxdomain",
	Doc: `report auxints that may lie outside the range their op accepts

Shift and rotate ops take their count in the auxint, and the count must
lie in [0, width-1]: AMD64Ops.go says SHLQconst's "auxint must be in the
range 0 to 63", LOONG64Ops.go that SLLVconst's "auxInt should be in the
range 0 to 63". Out of range, the instruction may shift by the count
modulo the width, the assembler may reject it, or codegen may Fatalf. A
rule that computes a count must make sure it is in range. In

	(SHLQconst [c] (ADDQ x x)) => (SHLQconst [c+1] x)

c = 63 gives SHLQconst [64], which shifts by 0, so (x+x)<<63, which is 0,
becomes x. The fix is the condition c < 63.

Domains are treated as invariants: an op's auxint in a match is assumed to
be in its domain, and every op a rule creates must be in its domain, given
that and the rule's condition. Rules for the same op are tried in order,
so a rule fires only if the earlier rules that would match the same value
did not: in

	(SLLV _ (MOVVconst [c])) && uint64(c)>=64 => (MOVVconst [0])
	(SLLV x (MOVVconst [c])) => (SLLVconst x [c])

the second rule's c is in [0, 63]. A diagnostic gives values of the
rule's variables that satisfy all this and produce the bad auxint.
Conditions that bound a count by a type's size (c < t.Size()*8-1) are
not checked, since the types an op's values have are not recorded.

Three related mistakes are reported too:

  - Turning a shift by a register into a shift by an auxint, when they
    disagree for some count. PPC64Ops.go says SLD shifts by arg1&127, so
    a count of 64 gives 0, but

	(SLD x (MOVDconst [c])) => (SLDconst [c&63 | (c>>6&1*63)] x)

    shifts by 63. (That is right for SRAD, which fills with the sign.)
  - Masking a count that is already in its op's domain into a narrower
    one. (SRLI <t> [x] (MOVWUreg y)) => (SRLIW <t> [int64(x&31)] y)
    turns a shift by 40, which must give 0, into a shift by 8. Masking a
    register's count, as in (SLL x (MOVWconst [c])) => (SLLconst x [c&31]),
    is the previous check's business.
  - A Go shift by a negative count in a result's auxint or aux, which
    panics in the compiler: (Lsh64x64 (Const64 [c]) (Const64 [d])) =>
    (Const64 [c << d]) needs d >= 0.

Domains and register shift semantics come from the op comments in
<arch>Ops.go; see domains and regShifts.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			return fmt.Errorf("%s: %v", set, err)
		}
		var doms map[string]domain
		var regs map[string]regShift
		if !set.Arch.Generic {
			doms = domains(pass.Ops.Dir, set.Arch.Name)
			regs = regShifts(pass.Ops.Dir, set.Arch.Name)
		}
		for _, r := range set.Rules {
			tr := res.Rule(r)
			if tr == nil {
				continue
			}
			c := &checker{pass: pass, res: res, info: res.Info, r: r, tr: tr, doms: doms, regs: regs}
			c.check()
		}
	}
	return nil
}

type checker struct {
	pass *analysis.Pass
	res  *typecheck.Result
	info *types.Info
	r    *rules.Rule
	tr   *typecheck.Rule
	doms map[string]domain
	regs map[string]regShift

	f *facts.Facts
}

// facts returns the facts of the rule, computing them the first time.
func (c *checker) facts() *facts.Facts {
	if c.f != nil {
		return c.f
	}
	f := facts.New(c.res, c.r)
	for _, m := range c.r.MatchValues() {
		m.Walk(func(v *rules.Value) bool {
			d, ok := c.domain(v)
			if !ok || v.AuxInt == "" || v.AuxInt == "_" {
				return true
			}
			// A matched op's auxint is in its domain, whether the
			// match binds it ([c]) or compares it ([64-c]).
			if rules.IsVarText(v.AuxInt) {
				f = f.AssumeVar(v.AuxInt, facts.Range(d.lo, d.hi))
			} else if e := c.tr.Expr(v, typecheck.AuxInt); e != nil {
				f = f.AssumeIn(e, facts.Range(d.lo, d.hi))
			}
			return true
		})
	}
	c.f = prior.Facts(c.res, c.r, f)
	return c.f
}

// domain returns the domain of v's auxint, if v is an op with a
// documented domain and an integer auxint.
func (c *checker) domain(v *rules.Value) (domain, bool) {
	if v.Op == nil || v.Op.IsGeneric() {
		return domain{}, false
	}
	switch v.Op.AuxIntType {
	case "int8", "int16", "int32", "int64", "uint8":
	default:
		return domain{}, false
	}
	d, ok := c.doms[v.Op.Name]
	return d, ok
}

func (c *checker) check() {
	c.regToConst()
	for _, v := range c.r.ResultValues() {
		v.Walk(func(v *rules.Value) bool {
			if v.IsLeaf() {
				return true
			}
			if d, ok := c.domain(v); ok {
				c.created(v, d)
				c.masked(v)
			}
			for _, fld := range []typecheck.Field{typecheck.AuxInt, typecheck.Aux} {
				if e := c.tr.Expr(v, fld); e != nil {
					c.panics(e)
				}
			}
			return true
		})
	}
	if rb := c.r.ResultBlock; rb != nil {
		for _, fld := range []typecheck.Field{typecheck.AuxInt, typecheck.Aux} {
			if e := c.tr.Expr(rb, fld); e != nil {
				c.panics(e)
			}
		}
	}
}

// masked reports a count in v's auxint that is a matched op's count,
// masked to fewer bits than that op's domain needs, as in
// (SRLI <t> [x] (MOVWUreg y)) => (SRLIW <t> [int64(x&31)] y).
func (c *checker) masked(v *rules.Value) {
	e := c.tr.Expr(v, typecheck.AuxInt)
	if e == nil {
		return
	}
	ast.Inspect(e, func(n ast.Node) bool {
		x, ok := n.(*ast.BinaryExpr)
		if !ok || x.Op != token.AND {
			return true
		}
		for _, pair := range [][2]ast.Expr{{x.X, x.Y}, {x.Y, x.X}} {
			m, ok := c.constant(pair[1])
			if !ok {
				continue
			}
			src, d, ok := c.domainVar(pair[0])
			if !ok || d.hi <= m || (m+1)&m != 0 {
				continue
			}
			f := c.facts()
			if f.In(pair[0], 0, m) {
				continue
			}
			var got *big.Int
			w := witness.Search(f, c.res, c.r, func(vals map[types.Object]any) bool {
				y, ok := f.Eval(pair[0], vals)
				got, _ = y.(*big.Int)
				return ok && got != nil && (got.Sign() < 0 || got.Cmp(big.NewInt(m)) > 0)
			})
			if w == nil {
				continue
			}
			masked := new(big.Int).And(got, big.NewInt(m))
			c.pass.Reportf(c.r.Pos, "%s [%s] masks %s's count %s, which is in [%d, %d] (%s), to %d bits: %s becomes %s, a different shift",
				v.OpName, types.ExprString(e), src.OpName, types.ExprString(pair[0]), d.lo, d.hi, d.src, bits.Len64(uint64(m)), got, masked)
		}
		return true
	})
}

// constant returns the value of e, if it is an integer constant.
func (c *checker) constant(e ast.Expr) (int64, bool) {
	tv, ok := c.info.Types[e]
	if !ok || tv.Value == nil {
		return 0, false
	}
	return constant.Int64Val(constant.ToInt(tv.Value))
}

// domainVar returns the matched op whose auxint e is, possibly
// converted, and its domain, if it has one.
func (c *checker) domainVar(e ast.Expr) (*rules.Value, domain, bool) {
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.CallExpr:
			tv, ok := c.info.Types[x.Fun]
			if !ok || !tv.IsType() || len(x.Args) != 1 {
				return nil, domain{}, false
			}
			e = x.Args[0]
			continue
		case *ast.Ident:
			v := c.boundBy(x)
			if v == nil {
				return nil, domain{}, false
			}
			d, ok := c.domain(v)
			return v, d, ok
		}
		return nil, domain{}, false
	}
}

// panics reports shifts in e, a result's auxint or aux, by a count that
// may be negative, which panics, crashing the compiler. (The divzero
// analyzer reports division by zero.)
func (c *checker) panics(e ast.Expr) {
	ast.Inspect(e, func(n ast.Node) bool {
		x, ok := n.(*ast.BinaryExpr)
		if !ok || x.Op != token.SHL && x.Op != token.SHR {
			return true
		}
		if b, ok := c.info.TypeOf(x.Y).Underlying().(*types.Basic); !ok || b.Info()&types.IsUnsigned != 0 {
			return true
		}
		if _, ok := c.constant(x.Y); ok {
			return true
		}
		f := c.facts()
		if f.In(x.Y, 0, math.MaxInt64) {
			return true
		}
		var got *big.Int
		w := witness.Search(f, c.res, c.r, func(vals map[types.Object]any) bool {
			y, ok := f.Eval(x.Y, vals)
			got, _ = y.(*big.Int)
			return ok && got != nil && got.Sign() < 0
		})
		if w == nil {
			return true
		}
		c.pass.Reportf(c.r.Pos, "%s panics (negative shift amount) when %s: %s is %s",
			types.ExprString(x), w, types.ExprString(x.Y), got)
		return true
	})
}

// created checks the auxint of result value v, whose op has domain d.
func (c *checker) created(v *rules.Value, d domain) {
	e := c.tr.Expr(v, typecheck.AuxInt)
	if e == nil {
		return
	}
	if !c.computed(e) {
		return
	}
	f := c.facts()
	if f.In(e, d.lo, d.hi) {
		return
	}
	if c.typeDependent() {
		// The condition bounds the count by the size of a type, such
		// as c < t.Size()*8-1, which holds for the types the op's
		// values have. Those are not recorded anywhere.
		return
	}
	var got *big.Int
	w := witness.Search(f, c.res, c.r, func(vals map[types.Object]any) bool {
		x, ok := f.Eval(e, vals)
		got, _ = x.(*big.Int)
		return ok && got != nil && (got.Cmp(big.NewInt(d.lo)) < 0 || got.Cmp(big.NewInt(d.hi)) > 0)
	})
	if w == nil {
		return
	}
	c.pass.Reportf(c.r.Pos, "%s [%s] is %s, outside [%d, %d] (%s), when %s",
		v.OpName, types.ExprString(e), got, d.lo, d.hi, d.src, w)
}

// computed reports whether e computes a new auxint from the match: it
// refers to a match variable, and is not merely a copy (possibly
// converted) of an auxint, or a field of an aux, of a matched op whose
// domain is unknown. Such a copy, as in
//
//	(CMPshiftLL (MOVWconst [c]) x [d]) => (InvertFlags (CMPconst [c] (SLLconst <x.Type> x [d])))
//
// keeps whatever invariant the matched op maintains. An auxint of a
// constant (MOVWconst [c]) is a value, not a count, and is checked.
func (c *checker) computed(e ast.Expr) bool {
	vars := false
	ast.Inspect(e, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && c.isMatchVar(id) {
			vars = true
		}
		return !vars
	})
	if !vars {
		return false
	}
	for {
		switch x := ast.Unparen(e).(type) {
		case *ast.CallExpr:
			tv, ok := c.info.Types[x.Fun]
			if !ok || !tv.IsType() || len(x.Args) != 1 {
				return true
			}
			e = x.Args[0]
			continue
		case *ast.SelectorExpr:
			e = x.X
			continue
		case *ast.Ident:
			v := c.boundBy(x)
			return v == nil || v.Op == nil || v.Op.ArgLength == 0 || c.hasDomain(v)
		}
		return true
	}
}

func (c *checker) hasDomain(v *rules.Value) bool {
	_, ok := c.domain(v)
	return ok
}

// isMatchVar reports whether id is one of the rule's match variables.
func (c *checker) isMatchVar(id *ast.Ident) bool {
	obj := c.info.Uses[id]
	return obj != nil && c.tr.Vars[id.Name] == obj && c.r.MatchVars()[id.Name] != nil
}

// boundBy returns the match value whose auxint or aux id binds.
func (c *checker) boundBy(id *ast.Ident) *rules.Value {
	if !c.isMatchVar(id) {
		return nil
	}
	for _, o := range c.r.MatchVars()[id.Name] {
		if o.Kind == rules.OccAuxInt || o.Kind == rules.OccAux {
			return o.Value
		}
	}
	return nil
}

// typeDependent reports whether the condition depends on the size of a
// type.
func (c *checker) typeDependent() bool {
	found := false
	if c.tr.Cond != nil {
		ast.Inspect(c.tr.Cond, func(n ast.Node) bool {
			if sel, ok := n.(*ast.SelectorExpr); ok && sel.Sel.Name == "Size" {
				found = true
			}
			return !found
		})
	}
	return found
}

// regToConst checks a rule that turns a shift by a constant in a
// register into a shift by an auxint:
//
//	(SLD x (MOVDconst [c])) => (SLDconst [c&63 | (c>>6&1*63)] x)
//
// The register shift uses its count modulo some power of two (SLD uses
// arg1&127), and a count that is at least the width gives 0 (or, for an
// arithmetic shift, the sign); the auxint shift's count is in [0,
// width-1]. The two must agree for every count the condition admits:
// here c = 64 makes SLD give 0 but SLDconst shift by 63.
func (c *checker) regToConst() {
	m, r := c.r.Match, c.r.Result
	if m == nil || r == nil || m.Op == nil || r.Op == nil || len(m.Args) != 2 || len(r.Args) != 1 {
		return
	}
	reg, ok := c.regs[m.Op.Name]
	if !ok || !constOf(m.Op.Name, r.Op.Name) {
		return
	}
	d, ok := c.domain(r)
	if !ok || d.lo != 0 {
		return
	}
	x, k := m.Args[0], m.Args[1]
	if !x.IsVar() || r.Args[0].Text != x.Name || k.Op == nil || k.Op.ArgLength != 0 || !rules.IsVarText(k.AuxInt) {
		return
	}
	e := c.tr.Expr(r, typecheck.AuxInt)
	count := c.tr.Vars[k.AuxInt]
	if e == nil || count == nil {
		return
	}
	w := d.hi + 1 // the operation's width
	f := c.facts()
	var cv, ev *big.Int
	var want string
	wit := witness.Search(f, c.res, c.r, func(vals map[types.Object]any) bool {
		cv, _ = vals[count].(*big.Int)
		v, ok := f.Eval(e, vals)
		ev, _ = v.(*big.Int)
		if !ok || cv == nil || ev == nil || ev.Sign() < 0 || ev.Int64() >= w {
			return false // or a domain violation, reported separately
		}
		n := new(big.Int).And(cv, big.NewInt(reg.mod-1)).Int64()
		switch {
		case reg.kind == rotate:
			if n%w == ev.Int64() {
				return false
			}
			want = fmt.Sprintf("rotates by %d", n%w)
		case n < w:
			if n == ev.Int64() {
				return false
			}
			want = fmt.Sprintf("shifts by %d", n)
		case reg.kind == shiftRightArith:
			if ev.Int64() == w-1 {
				return false
			}
			want = fmt.Sprintf("shifts by %d, the same as by %d", n, w-1)
		default:
			want = fmt.Sprintf("shifts by %d, giving 0", n)
		}
		return true
	})
	if wit == nil {
		return
	}
	c.pass.Reportf(c.r.Pos, "%s with count %s=%s %s (it uses the count mod %d, %s), but %s [%s] is %s",
		m.OpName, k.AuxInt, cv, want, reg.mod, reg.src, r.OpName, types.ExprString(e), ev)
}

// constOf reports whether op is the auxint form of register op reg:
// SLD and SLDconst, SLL and SLLI, SLLW and SLLIW.
func constOf(reg, op string) bool {
	return op == reg+"const" || op == reg+"I" || strings.HasSuffix(reg, "W") && op == strings.TrimSuffix(reg, "W")+"IW"
}
