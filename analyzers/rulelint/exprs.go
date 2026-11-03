package rulelint

import (
	"go/ast"
	"go/constant"
	"go/token"
)

// precedence reports expressions whose grouping in Go differs from the
// grouping in C, where most of the compiler's bit-twiddling idioms come
// from. Go gives &, &^, <<, >>, *, /, and % the same precedence and
// associates them left, while C binds * / % tighter than << >>, and those
// tighter than &. So in Go d &^ 1<<c is (d &^ 1) << c, not d &^ (1<<c),
// which clears bit c of d; and 1 << c * 8 is (1 << c) * 8, not 1 << (c*8).
//
// & or &^ under * / % is not reported: c>>6&1*63, which multiplies a bit
// by 63, is a deliberate idiom, and the C reading, c>>6 & (1*63), is
// implausible.
func (c *checker) precedence() {
	for _, e := range c.exprs() {
		ast.Inspect(e, func(n ast.Node) bool {
			b, ok := n.(*ast.BinaryExpr)
			if !ok {
				return true
			}
			x, ok := b.X.(*ast.BinaryExpr) // not ast.Unparen: parentheses are deliberate
			if !ok || cRank(x.Op) == 0 || cRank(b.Op) != cRank(x.Op)+1 {
				return true
			}
			c.report("%s means (%s) %s %s, since %s and %s have the same precedence in Go (unlike C); parenthesize",
				str(b), str(x), b.Op, str(b.Y), x.Op, b.Op)
			return true
		})
	}
}

// cRank returns the C precedence rank of a Go operator with Go
// precedence 5, higher binding tighter, treating &^ like &. It returns 0
// for other operators.
func cRank(op token.Token) int {
	switch op {
	case token.MUL, token.QUO, token.REM:
		return 3
	case token.SHL, token.SHR:
		return 2
	case token.AND, token.AND_NOT:
		return 1
	}
	return 0
}

// remainder reports conditions x%k == r (or !=) with |r| >= k, which are
// constant.
func (c *checker) remainder() {
	if c.tr.Cond == nil {
		return
	}
	ast.Inspect(c.tr.Cond, func(n ast.Node) bool {
		b, ok := n.(*ast.BinaryExpr)
		if !ok || b.Op != token.EQL && b.Op != token.NEQ {
			return true
		}
		mod, r := b.X, b.Y
		if _, ok := ast.Unparen(mod).(*ast.BinaryExpr); !ok {
			mod, r = r, mod
		}
		m, ok := ast.Unparen(mod).(*ast.BinaryExpr)
		if !ok || m.Op != token.REM {
			return true
		}
		kv, rv := c.res.Info.Types[m.Y].Value, c.res.Info.Types[r].Value
		if kv == nil || rv == nil || kv.Kind() != constant.Int || rv.Kind() != constant.Int {
			return true
		}
		absK, absR := abs(kv), abs(rv)
		if constant.Compare(absK, token.GTR, constant.MakeInt64(0)) && constant.Compare(absR, token.GEQ, absK) {
			c.report("%s is always %t: a remainder mod %s is never %s", str(b), b.Op == token.NEQ, kv, rv)
		}
		return true
	})
}

func abs(v constant.Value) constant.Value {
	if constant.Sign(v) < 0 {
		return constant.UnaryOp(token.SUB, v, 0)
	}
	return v
}
