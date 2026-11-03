package facts

import (
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math/big"
	"sync"
)

// Helpers that only choose among constants, such as
//
//	func MoveSize(align int64, c *Config) int64 {
//		switch {
//		case align%8 == 0 && c.PtrSize == 8:
//			return 8
//		...
//		}
//		return 1
//	}
//
// are not inlinable, but their value is bounded by the constants they
// return.

var constReturnCache struct {
	sync.Mutex
	m map[*types.Func]*Interval // nil if not such a helper
}

// constReturns returns the range of the values that fn returns, if fn
// has one integer result, each of its return statements returns an
// integer literal, and it defers nothing.
func constReturns(fset *token.FileSet, fn *types.Func) (Interval, bool) {
	constReturnCache.Lock()
	defer constReturnCache.Unlock()
	if iv, ok := constReturnCache.m[fn]; ok {
		if iv == nil {
			return Interval{}, false
		}
		return *iv, true
	}
	if constReturnCache.m == nil {
		constReturnCache.m = make(map[*types.Func]*Interval)
	}
	var res *Interval
	if iv, ok := buildConstReturns(fset, fn); ok {
		res = &iv
	}
	constReturnCache.m[fn] = res
	if res == nil {
		return Interval{}, false
	}
	return *res, true
}

func buildConstReturns(fset *token.FileSet, fn *types.Func) (Interval, bool) {
	sig := fn.Signature()
	if sig.Results().Len() != 1 || sig.TypeParams().Len() > 0 {
		return Interval{}, false
	}
	tr, ok := TypeRange(sig.Results().At(0).Type())
	if !ok {
		return Interval{}, false
	}
	pos := fset.Position(fn.Pos())
	inlines.Lock()
	if inlines.files == nil {
		inlines.m = make(map[inlineKey]*inlined)
		inlines.files = make(map[string]*parsedFile)
	}
	pf := parseFile(pos.Filename)
	inlines.Unlock()
	if pf == nil {
		return Interval{}, false
	}
	var fd *ast.FuncDecl
	for _, d := range pf.file.Decls {
		if d, ok := d.(*ast.FuncDecl); ok && d.Name.Name == fn.Name() && pf.fset.Position(d.Name.Pos()).Offset == pos.Offset {
			fd = d
		}
	}
	if fd == nil || fd.Body == nil {
		return Interval{}, false
	}
	var lo, hi *big.Int
	ok = true
	n := 0
	ast.Inspect(fd.Body, func(node ast.Node) bool {
		switch node := node.(type) {
		case *ast.FuncLit:
			return false
		case *ast.DeferStmt:
			ok = false // it may change a named result
			return false
		case *ast.ReturnStmt:
			n++
			x, isConst := intLiteral(node)
			if !isConst {
				ok = false
				return false
			}
			if lo == nil || x.Cmp(lo) < 0 {
				lo = x
			}
			if hi == nil || x.Cmp(hi) > 0 {
				hi = x
			}
		}
		return ok
	})
	if !ok || n == 0 {
		return Interval{}, false
	}
	iv := Interval{lo, hi}
	if !iv.Within(tr) {
		return Interval{}, false
	}
	return iv, true
}

// intLiteral returns the value of ret's result if it is an integer
// literal, possibly negated.
func intLiteral(ret *ast.ReturnStmt) (*big.Int, bool) {
	if len(ret.Results) != 1 {
		return nil, false
	}
	e := unparen(ret.Results[0])
	neg := false
	if u, ok := e.(*ast.UnaryExpr); ok && u.Op == token.SUB {
		neg, e = true, unparen(u.X)
	}
	lit, ok := e.(*ast.BasicLit)
	if !ok || lit.Kind != token.INT {
		return nil, false
	}
	v := constant.MakeFromLiteral(lit.Value, lit.Kind, 0)
	x, ok := new(big.Int).SetString(v.ExactString(), 10)
	if !ok {
		return nil, false
	}
	if neg {
		x.Neg(x)
	}
	return x, true
}
