package extelim

import (
	"go/ast"
	"go/parser"
	"go/token"
	"path/filepath"
	"strings"
	"sync"

	"github.com/josharian/unruly/ops"
)

// zeroUpperOps returns the ops whose values rewrite.go's zeroUpperNBits
// helper (N = bits) accepts unconditionally: those whose zeroUpperBits
// attribute is at least bits, and, in trees from before that attribute,
// those listed in the helper's switch with a bare "return true".
func zeroUpperOps(arch *ops.Arch, bits int) map[*ops.Op]bool {
	m := map[*ops.Op]bool{}
	for _, op := range arch.Ops {
		if int(op.ZeroUpperBits) >= bits {
			m[op] = true
		}
	}
	for _, name := range helperCases(arch.Tables().Dir)[bits] {
		if op, ok := strings.CutPrefix(name, "Op"+arch.Name); ok {
			if o := arch.Op(op); o != nil {
				m[o] = true
			}
		}
	}
	return m
}

var helperCache struct {
	sync.Mutex
	m map[string]map[int][]string
}

// helperCases parses rewrite.go next to genDir and returns, for each N,
// the op constants in the cases of zeroUpperNBits that return true.
func helperCases(genDir string) map[int][]string {
	helperCache.Lock()
	defer helperCache.Unlock()
	if m, ok := helperCache.m[genDir]; ok {
		return m
	}
	if helperCache.m == nil {
		helperCache.m = map[string]map[int][]string{}
	}
	m := map[int][]string{}
	helperCache.m[genDir] = m
	f, err := parser.ParseFile(token.NewFileSet(), filepath.Join(filepath.Dir(genDir), "rewrite.go"), nil, 0)
	if err != nil {
		return m
	}
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Body == nil {
			continue
		}
		sm := zeroUpperRE.FindStringSubmatch(lower(fd.Name.Name))
		if sm == nil {
			continue
		}
		n := 0
		for _, c := range sm[1] {
			n = n*10 + int(c-'0')
		}
		ast.Inspect(fd.Body, func(nd ast.Node) bool {
			cc, ok := nd.(*ast.CaseClause)
			if !ok {
				return true
			}
			if len(cc.Body) != 1 {
				return false
			}
			ret, ok := cc.Body[0].(*ast.ReturnStmt)
			if !ok || len(ret.Results) != 1 {
				return false
			}
			if id, ok := ret.Results[0].(*ast.Ident); !ok || id.Name != "true" {
				return false
			}
			for _, e := range cc.List {
				switch e := e.(type) {
				case *ast.Ident:
					m[n] = append(m[n], e.Name)
				case *ast.SelectorExpr:
					m[n] = append(m[n], e.Sel.Name)
				}
			}
			return false
		})
	}
	return m
}
