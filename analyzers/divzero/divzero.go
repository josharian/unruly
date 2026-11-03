// Package divzero defines an analyzer that reports integer divisions in
// rules whose divisor may be zero.
package divzero

import (
	"go/ast"
	"go/token"
	"go/types"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "divzero",
	Doc: `report integer divisions by a divisor that may be zero

A rule's condition and results are Go code that the compiler runs. An
integer / or % in them whose divisor is 0 panics the compiler. Constant
folds are the usual culprit:

	(Select1 (DIVV (MOVVconst [c]) (MOVVconst [d]))) => (MOVVconst [c/d])

crashes the compiler on a division by a constant zero, which a program
may well contain in code that never runs. The guard must be on the
divisor actually used:

	(DIVW (MOVDconst [c]) (MOVDconst [d])) && d != 0 => (MOVDconst [int64(uint32(int32(c)/int32(d)))])

still divides by zero for d = 1<<32, since int32(d) is 0.

A division in the condition must be guarded by conditions evaluated
before it: in c%d == 0 && d != 0, the guard comes too late.
Floating-point division is not checked.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		var res *typecheck.Result
		for _, r := range set.Rules {
			if res == nil {
				var err error
				if res, err = typecheck.Check(set); err != nil {
					return err
				}
			}
			tr := res.Rule(r)
			if tr == nil {
				continue
			}
			if tr.Cond != nil {
				for _, d := range divisors(res.Info, tr.Cond) {
					if !facts.At(res, r, d.Y).NonZero(d.Y) {
						report(pass, r, d, "the condition")
						break
					}
				}
			}
			if d := unguarded(res, r, resultExprs(r, tr)); d != nil {
				report(pass, r, d, "the result")
			}
		}
	}
	return nil
}

// unguarded returns a division in es, which r evaluates when it fires,
// whose divisor r's condition does not prove nonzero.
func unguarded(res *typecheck.Result, r *rules.Rule, es []ast.Expr) *ast.BinaryExpr {
	var f *facts.Facts
	for _, e := range es {
		for _, d := range divisors(res.Info, e) {
			if f == nil {
				f = facts.New(res, r)
			}
			if !f.NonZero(d.Y) {
				return d
			}
		}
	}
	return nil
}

func report(pass *analysis.Pass, r *rules.Rule, d *ast.BinaryExpr, where string) {
	pass.Reportf(r.Pos, "%s in %s divides by zero if %s is 0, panicking the compiler; the condition must ensure that it is not",
		types.ExprString(d), where, types.ExprString(d.Y))
}

// resultExprs returns the Go expressions of r's result that the
// rewrite evaluates: auxints, auxes, and {code}.
func resultExprs(r *rules.Rule, tr *typecheck.Rule) []ast.Expr {
	var es []ast.Expr
	add := func(node any, f typecheck.Field) {
		if e := tr.Expr(node, f); e != nil {
			es = append(es, e)
		}
	}
	walk := func(v *rules.Value) {
		v.Walk(func(v *rules.Value) bool {
			add(v, typecheck.AuxInt)
			add(v, typecheck.Aux)
			return true
		})
	}
	if r.Result != nil {
		walk(r.Result)
	}
	if b := r.ResultBlock; b != nil {
		add(b, typecheck.AuxInt)
		add(b, typecheck.Aux)
		for _, c := range b.Controls {
			walk(c)
		}
	}
	if tr.Code != nil {
		es = append(es, tr.Code)
	}
	return es
}

// divisors returns the integer divisions and remainders in e whose
// divisor is not a constant.
func divisors(info *types.Info, e ast.Expr) []*ast.BinaryExpr {
	var ds []*ast.BinaryExpr
	ast.Inspect(e, func(n ast.Node) bool {
		b, ok := n.(*ast.BinaryExpr)
		if !ok || b.Op != token.QUO && b.Op != token.REM {
			return true
		}
		t := info.TypeOf(b)
		if t == nil {
			return true // ill-typed
		}
		if t, ok := t.Underlying().(*types.Basic); !ok || t.Info()&types.IsInteger == 0 {
			return true
		}
		if tv, ok := info.Types[b.Y]; ok && tv.Value != nil {
			return true // a constant zero divisor does not compile
		}
		ds = append(ds, b)
		return true
	})
	return ds
}
