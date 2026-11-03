package facts

import (
	"go/ast"
	"go/token"

	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// At returns the facts that hold when sub-expression e of rule r's
// condition is evaluated: only the conditions that Go's short-circuit
// evaluation has already checked. In
//
//	d != 0 && c%d == 0
//
// d is nonzero at c%d, but in c%d == 0 && d != 0 it is not. If e is not
// in r's condition, At returns facts that know nothing of the
// condition.
func At(res *typecheck.Result, r *rules.Rule, e ast.Expr) *Facts {
	f := &Facts{res: res, root: &env{info: res.Info}}
	if tr := res.Rule(r); tr != nil && tr.Cond != nil {
		path, _ := pathTo(tr.Cond, e)
		for i, n := range path[:max(len(path)-1, 0)] {
			b, ok := n.(*ast.BinaryExpr)
			if !ok || path[i+1] != b.Y {
				continue
			}
			switch b.Op {
			case token.LAND:
				f.nots = append(f.nots, assumption{e: b.X, en: f.root, truth: true})
			case token.LOR:
				f.nots = append(f.nots, assumption{e: b.X, en: f.root, truth: false})
			}
		}
	}
	f.derive()
	return f
}

// pathTo returns the nodes from root down to e, inclusive.
func pathTo(root, e ast.Node) ([]ast.Node, bool) {
	var path []ast.Node
	found := false
	ast.Inspect(root, func(n ast.Node) bool {
		if found {
			return false
		}
		if n == nil {
			path = path[:len(path)-1]
			return false
		}
		path = append(path, n)
		if n == e {
			found = true
			return false
		}
		return true
	})
	return path, found
}
