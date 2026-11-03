// Package rulelint reports rules whose Go expressions or match shapes say
// something other than what their author evidently meant.
package rulelint

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "rulelint",
	Doc: `report rules whose text evidently does not mean what was intended

Each check targets a kind of mistake that has caused miscompiles,
compiler crashes, or dropped linker references:

  - Size in bits: Type.Size() is in bytes, so in
    (MOVHZreg (SRWconst [c] x)) && x.Type.Size() <= 16 => (SRWconst [c] x)
    the condition is always true (x is in a general-purpose register, at
    most 8 bytes) and the zero extension is dropped for every c, though a
    later rule makes the same rewrite only when c>=16. (An always-true
    condition is reported only with such evidence that it was needed; an
    always-false one makes the rule dead.)
  - Precedence: &, &^, <<, >>, and * share a precedence in Go but not in
    C, so d &^ 1<<c is (d &^ 1) << c, not d &^ (1<<c), and 1 << c * 8 is
    (1 << c) * 8.
  - Impossible remainder: x%8 == 9 is always false, and x%2 == 8 too.
  - Fixed arity on a variadic op: (IMake _typ (StructMake val)) matches only
    one-field structs; with val otherwise unused, the author meant
    (StructMake ___).
  - One-sided mergeSym: a condition that tests only sym1 (as in
    !isAuto(sym1)) while the result uses mergeSym(sym1, sym2), whose symbol
    usually comes from sym2.
  - Empty aggregates: a StructMake or ArrayMake1 of the rule's own type
    needs t.Size() > 0; zero-sized values must be (Empty). (Checked only
    in trees that have the Empty op.)
  - IsPtr instead of IsPtrShaped: decomposing a direct-interface aggregate,
    (StructMake x) && x.Type.IsPtr() => x misses maps, chans, and funcs.
  - Synthesized symbols: a result {aux} built by a helper from a symbol and
    an offset, such as {ptrElem(s, off)}, makes a new linker reference that
    must be recorded on the function; the helper needs b.Func or v.`,
	Run: run,
}

type checker struct {
	pass *analysis.Pass
	res  *typecheck.Result
	rule *rules.Rule
	tr   *typecheck.Rule
}

func (c *checker) report(format string, args ...any) {
	c.pass.Reportf(c.rule.Pos, format, args...)
}

var checks = []func(*checker){
	(*checker).sizeUnits,
	(*checker).precedence,
	(*checker).remainder,
	(*checker).variadicArity,
	(*checker).mergeSym,
	(*checker).emptyMake,
	(*checker).ptrShaped,
	(*checker).synthSym,
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
			c := &checker{pass: pass, res: res, rule: r, tr: tr}
			for _, check := range checks {
				check(c)
			}
		}
	}
	return nil
}

// exprs returns all of the rule's Go expressions.
func (c *checker) exprs() []ast.Expr {
	var es []ast.Expr
	add := func(node any, fields ...typecheck.Field) {
		for _, f := range fields {
			if e := c.tr.Expr(node, f); e != nil {
				es = append(es, e)
			}
		}
	}
	walk := func(vs []*rules.Value) {
		for _, v := range vs {
			v.Walk(func(v *rules.Value) bool {
				add(v, typecheck.Type, typecheck.AuxInt, typecheck.Aux, typecheck.Name)
				return true
			})
		}
	}
	walk(c.rule.MatchValues())
	walk(c.rule.ResultValues())
	if c.rule.IsBlock() {
		add(c.rule.MatchBlock, typecheck.AuxInt, typecheck.Aux)
		add(c.rule.ResultBlock, typecheck.AuxInt, typecheck.Aux)
	}
	for _, e := range []ast.Expr{c.tr.Cond, c.tr.Code, c.tr.Placement} {
		if e != nil {
			es = append(es, e)
		}
	}
	return es
}

// conjuncts returns the && operands of the condition.
func (c *checker) conjuncts() []ast.Expr {
	var out []ast.Expr
	var split func(e ast.Expr)
	split = func(e ast.Expr) {
		if b, ok := ast.Unparen(e).(*ast.BinaryExpr); ok && b.Op == token.LAND {
			split(b.X)
			split(b.Y)
			return
		}
		out = append(out, e)
	}
	if c.tr.Cond != nil {
		split(c.tr.Cond)
	}
	return out
}

// funcName returns the name of the function or method that call calls,
// without any package qualifier, or "".
func funcName(call *ast.CallExpr) string {
	switch fn := ast.Unparen(call.Fun).(type) {
	case *ast.Ident:
		return fn.Name
	case *ast.SelectorExpr:
		return fn.Sel.Name
	}
	return ""
}

// uses reports whether identifier name occurs in any of es.
func uses(es []ast.Expr, name string) bool {
	found := false
	for _, e := range es {
		ast.Inspect(e, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && id.Name == name {
				found = true
			}
			return !found
		})
	}
	return found
}

func str(e ast.Expr) string { return types.ExprString(e) }
