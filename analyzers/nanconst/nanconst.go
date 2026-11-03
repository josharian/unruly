// Package nanconst reports constant folds that make a float constant NaN
// or otherwise depend on the host's floating-point behavior.
package nanconst

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "nanconst",
	Doc: `report float constant folds that can produce NaN or host-dependent results

SSA float constants (Const64F, F64Const, FMOVDconst, ...) must never be NaN:
ssacompile/check.go rejects them ("value has an AuxInt that encodes a NaN"),
and a NaN computed by the compiler has whatever sign and payload the host's
FPU gives it (Inf + -Inf is 0xfff8000000000000 on amd64 and
0x7ff8000000000000 on arm64), so the output depends on the machine the
compiler runs on. A fold whose result can be NaN must be guarded:

	(Add64F (Const64F [c]) (Const64F [d])) && c+d == c+d => (Const64F [c+d])

Without the guard, c=+Inf, d=-Inf folds to a NaN constant. Matched float
constants are never NaN, so negation, math.Abs, math.Floor and the like,
float32/float64 conversions, and arithmetic with a nonzero finite literal
(1/c) need no guard. The recognized guards are !math.IsNaN(E), E == E, and,
for math.Sqrt(x), x >= 0.

Two related host dependencies are also reported, in any result expression:

  - A float32<->float64 conversion of a value that can be NaN: the host's
    conversion quiets signaling NaNs, changing their bits, so bit
    reinterpretation must use math.Float32bits/Float32frombits on the
    original value (historically, store-to-load forwarding of a float32
    sNaN changed its bits).
  - A float-to-integer conversion without a range guard: Go leaves
    out-of-range conversions implementation-defined, and arm64 saturates
    where amd64 produces 0x8000..., as in

	(Cvt64Fto32 (Const64F [c])) => (Const32 [int32(c)])

    which needs && c >= -1<<31 && c < 1<<31.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			return fmt.Errorf("%s: %v", set, err)
		}
		for _, r := range set.Rules {
			tr := res.Rule(r)
			if tr == nil {
				continue
			}
			c := &checker{pass: pass, info: res.Info, rule: r, tr: tr, conds: conjuncts(tr.Cond)}
			for _, v := range r.ResultValues() {
				v.Walk(func(v *rules.Value) bool {
					c.value(v)
					return true
				})
			}
		}
	}
	return nil
}

type checker struct {
	pass  *analysis.Pass
	info  *types.Info
	rule  *rules.Rule
	tr    *typecheck.Rule
	conds []ast.Expr
}

func (c *checker) value(v *rules.Value) {
	if v.IsLeaf() {
		return
	}
	for _, f := range []typecheck.Field{typecheck.AuxInt, typecheck.Aux} {
		e := c.tr.Expr(v, f)
		if e == nil {
			continue
		}
		if f == typecheck.AuxInt && (v.Op.Aux == "Float32" || v.Op.Aux == "Float64") {
			if w := c.nan(e); w != "" && !c.guarded(e) {
				c.pass.Reportf(c.rule.Pos, "%s aux %s is NaN %s; guard with !math.IsNaN(%[2]s) (float constants must not be NaN)",
					v.OpName, str(e), w)
			}
		}
		c.conversions(e)
	}
}

// conversions reports host-dependent conversions within e.
func (c *checker) conversions(e ast.Expr) {
	ast.Inspect(e, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || len(call.Args) != 1 {
			return true
		}
		tv, ok := c.info.Types[call.Fun]
		if !ok || !tv.IsType() {
			return true
		}
		to, ok := tv.Type.Underlying().(*types.Basic)
		if !ok {
			return true
		}
		arg := call.Args[0]
		from, ok := c.typeOf(arg).(*types.Basic)
		if !ok || from.Info()&types.IsFloat == 0 || c.info.Types[arg].Value != nil {
			return true
		}
		switch {
		case to.Info()&types.IsFloat != 0 && to.Kind() != from.Kind():
			if w := c.nan(arg); w != "" && !c.guarded(arg) {
				c.pass.Reportf(c.rule.Pos, "%s quiets a signaling NaN, changing its bits (%s is NaN %s); use math.Float32bits/Float32frombits on the original bits",
					str(call), str(arg), w)
			}
		case to.Info()&types.IsInteger != 0:
			if !c.rangeGuarded(arg, to) {
				c.pass.Reportf(c.rule.Pos, "%s is implementation-defined when %s is NaN, infinite, or out of range (amd64 and arm64 hosts disagree); guard the range of %[2]s",
					str(call), str(arg))
			}
		}
		return true
	})
}

func (c *checker) typeOf(e ast.Expr) types.Type {
	t := c.info.TypeOf(e)
	if t == nil {
		return nil
	}
	return t.Underlying()
}

func (c *checker) isFloat(e ast.Expr) bool {
	b, ok := c.typeOf(e).(*types.Basic)
	return ok && b.Info()&types.IsFloat != 0
}

// nan reports whether float expression e can be NaN, given that the
// variables it uses can't be. If so, it returns a witness, such as
// "for c=+Inf, d=-Inf"; otherwise it returns "".
func (c *checker) nan(e ast.Expr) string {
	e = ast.Unparen(e)
	if tv := c.info.Types[e]; tv.Value != nil || !c.isFloat(e) {
		return "" // Go constants and non-floats are never NaN
	}
	switch e := e.(type) {
	case *ast.Ident:
		return "" // a match variable: a float aux is never NaN
	case *ast.UnaryExpr:
		return c.nan(e.X)
	case *ast.BinaryExpr:
		x, y := ast.Unparen(e.X), ast.Unparen(e.Y)
		if w := c.nan(x); w != "" {
			return w
		}
		if w := c.nan(y); w != "" {
			return w
		}
		// Both operands are non-NaN. Arithmetic with a finite literal
		// (nonzero for * and /) can't make NaN.
		switch e.Op {
		case token.ADD, token.SUB:
			if c.finite(x, false) || c.finite(y, false) {
				return ""
			}
		case token.MUL, token.QUO:
			if c.finite(x, true) || c.finite(y, true) {
				return ""
			}
		}
		return "for " + witness(e.Op, str(x), str(y))
	case *ast.CallExpr:
		if tv := c.info.Types[e.Fun]; tv.IsType() {
			// A conversion. From an integer, it isn't NaN.
			if !c.isFloat(e.Args[0]) {
				return ""
			}
			return c.nan(e.Args[0])
		}
		switch name := c.mathFunc(e); name {
		case "Abs", "Ceil", "Floor", "Trunc", "Round", "RoundToEven", "Copysign":
			return c.nan(e.Args[0])
		case "Max", "Min":
			if w := c.nan(e.Args[0]); w != "" {
				return w
			}
			return c.nan(e.Args[1])
		case "Inf":
			return ""
		case "Sqrt":
			if w := c.nan(e.Args[0]); w != "" {
				return w
			}
			if c.nonNegative(e.Args[0]) {
				return ""
			}
			return fmt.Sprintf("for %s=-1", str(e.Args[0]))
		case "Float64frombits":
			return fmt.Sprintf("for %s=0x7ff8000000000000", c.bits(e.Args[0]))
		case "Float32frombits":
			return fmt.Sprintf("for %s=0x7fc00000", c.bits(e.Args[0]))
		}
	}
	return "for some inputs"
}

// bits returns the bits argument e of math.Float64frombits or
// Float32frombits, without integer conversions: c for uint64(c).
func (c *checker) bits(e ast.Expr) string {
	e = ast.Unparen(e)
	if call, ok := e.(*ast.CallExpr); ok && len(call.Args) == 1 && c.info.Types[call.Fun].IsType() {
		if t, ok := c.typeOf(call.Args[0]).(*types.Basic); ok && t.Info()&types.IsInteger != 0 {
			return c.bits(call.Args[0])
		}
	}
	return str(e)
}

func witness(op token.Token, x, y string) string {
	switch op {
	case token.ADD:
		return fmt.Sprintf("%s=+Inf, %s=-Inf", x, y)
	case token.SUB:
		return fmt.Sprintf("%s=%s=+Inf", x, y)
	case token.MUL:
		return fmt.Sprintf("%s=0, %s=+Inf", x, y)
	case token.QUO:
		return fmt.Sprintf("%s=%s=0", x, y)
	}
	return "some inputs"
}

// finite reports whether e is a finite constant (nonzero, if nonzero is set).
func (c *checker) finite(e ast.Expr, nonzero bool) bool {
	v := c.info.Types[e].Value
	if v == nil {
		return false
	}
	f, _ := constant.Float64Val(constant.ToFloat(v))
	return !math.IsInf(f, 0) && !(nonzero && f == 0)
}

// mathFunc returns the name of the math package function that call calls, or "".
func (c *checker) mathFunc(call *ast.CallExpr) string {
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok {
		return ""
	}
	fn, ok := c.info.Uses[sel.Sel].(*types.Func)
	if !ok || fn.Pkg() == nil || fn.Pkg().Path() != "math" {
		return ""
	}
	return fn.Name()
}

// guarded reports whether the condition ensures that e is not NaN:
// it has a conjunct !math.IsNaN(e) or e == e, ignoring float conversions.
func (c *checker) guarded(e ast.Expr) bool {
	k := c.key(e)
	for _, cond := range c.conds {
		cond = ast.Unparen(cond)
		switch cond := cond.(type) {
		case *ast.UnaryExpr:
			call, ok := ast.Unparen(cond.X).(*ast.CallExpr)
			if cond.Op == token.NOT && ok && c.mathFunc(call) == "IsNaN" && c.key(call.Args[0]) == k {
				return true
			}
		case *ast.BinaryExpr:
			if cond.Op == token.EQL && c.key(cond.X) == k && c.key(cond.Y) == k {
				return true
			}
		}
	}
	return false
}

// nonNegative reports whether the condition has a conjunct e >= 0 or e > 0.
func (c *checker) nonNegative(e ast.Expr) bool {
	k := c.key(e)
	for _, cond := range c.conds {
		b, ok := ast.Unparen(cond).(*ast.BinaryExpr)
		if ok && (b.Op == token.GEQ || b.Op == token.GTR) && c.key(b.X) == k && c.isZero(b.Y) {
			return true
		}
	}
	return false
}

func (c *checker) isZero(e ast.Expr) bool {
	v := c.info.Types[e].Value
	return v != nil && constant.Sign(v) == 0
}

// rangeGuarded reports whether the condition bounds e above and below
// within the range of integer type to: conjuncts like e >= lo and e < hi
// (in either order of operands), where every value in [lo, hi) truncates
// to a value of type to.
func (c *checker) rangeGuarded(e ast.Expr, to *types.Basic) bool {
	lo, hi := intRange(to)
	if lo == nil {
		return false
	}
	one := constant.MakeInt64(1)
	loLess1 := constant.BinaryOp(lo, token.SUB, one)
	hiPlus1 := constant.BinaryOp(hi, token.ADD, one)
	k := c.key(e)
	var lower, upper bool
	for _, cond := range c.conds {
		b, ok := ast.Unparen(cond).(*ast.BinaryExpr)
		if !ok {
			continue
		}
		op := b.Op
		var bound constant.Value
		switch {
		case c.key(b.X) == k && c.info.Types[b.Y].Value != nil:
			bound = c.info.Types[b.Y].Value
		case c.key(b.Y) == k && c.info.Types[b.X].Value != nil:
			bound, op = c.info.Types[b.X].Value, mirror(op)
		default:
			continue
		}
		if bound.Kind() != constant.Int && bound.Kind() != constant.Float {
			continue
		}
		// Truncation toward zero maps (lo-1, hi+1) into [lo, hi].
		switch op {
		case token.GEQ:
			lower = lower || constant.Compare(bound, token.GTR, loLess1)
		case token.GTR:
			lower = lower || constant.Compare(bound, token.GEQ, loLess1)
		case token.LSS:
			upper = upper || constant.Compare(bound, token.LEQ, hiPlus1)
		case token.LEQ:
			upper = upper || constant.Compare(bound, token.LSS, hiPlus1)
		}
	}
	return lower && upper
}

// intRange returns the bounds of integer type t, taking int, uint, and
// uintptr to be 64 bits, or nils.
func intRange(t *types.Basic) (lo, hi constant.Value) {
	bits, signed := 0, t.Info()&types.IsUnsigned == 0
	switch t.Kind() {
	case types.Int8, types.Uint8:
		bits = 8
	case types.Int16, types.Uint16:
		bits = 16
	case types.Int32, types.Uint32:
		bits = 32
	case types.Int64, types.Uint64, types.Int, types.Uint, types.Uintptr:
		bits = 64
	default:
		return nil, nil
	}
	one := constant.MakeInt64(1)
	if !signed {
		return constant.MakeInt64(0), constant.BinaryOp(constant.Shift(one, token.SHL, uint(bits)), token.SUB, one)
	}
	lim := constant.Shift(one, token.SHL, uint(bits-1))
	return constant.UnaryOp(token.SUB, lim, 0), constant.BinaryOp(lim, token.SUB, one)
}

func mirror(op token.Token) token.Token {
	switch op {
	case token.GEQ:
		return token.LEQ
	case token.GTR:
		return token.LSS
	case token.LEQ:
		return token.GEQ
	case token.LSS:
		return token.GTR
	}
	return op
}

// key returns a canonical text for e, without parentheses and
// float-to-float conversions, which don't affect whether a value is NaN.
func (c *checker) key(e ast.Expr) string {
	e = ast.Unparen(e)
	if call, ok := e.(*ast.CallExpr); ok && len(call.Args) == 1 && c.info.Types[call.Fun].IsType() &&
		c.isFloat(call) && c.isFloat(call.Args[0]) {
		return c.key(call.Args[0])
	}
	return strings.ReplaceAll(types.ExprString(e), " ", "")
}

// conjuncts splits e into its && operands.
func conjuncts(e ast.Expr) []ast.Expr {
	if e == nil {
		return nil
	}
	if b, ok := ast.Unparen(e).(*ast.BinaryExpr); ok && b.Op == token.LAND {
		return append(conjuncts(b.X), conjuncts(b.Y)...)
	}
	return []ast.Expr{e}
}

func str(e ast.Expr) string { return types.ExprString(e) }
