package auxsign

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
)

// zeroExtended returns the ops of arch whose codegen zero-extends a
// signed auxint, mapped to the number of bits it keeps: the ops named in
// each case clause of the arch's codegen package
// (cmd/compile/internal/<arch>) whose body contains int64(uintN(v.AuxInt)).
// For example, s390x/ssa.go emits CMPUconst's immediate as
// int64(uint32(v.AuxInt)), so CMPUconst [-1] compares against 0xffffffff.
// It returns an empty map if there are none or the package is missing.
func zeroExtended(genDir, arch string) map[string]uint {
	key := genDir + "\x00" + arch
	if m, ok := zeroCache.Load(key); ok {
		return m.(map[string]uint)
	}
	m := loadZeroExtended(genDir, arch)
	zeroCache.Store(key, m)
	return m
}

var zeroCache sync.Map

func loadZeroExtended(genDir, arch string) map[string]uint {
	pkg := strings.ToLower(arch)
	if arch == "386" {
		pkg = "x86"
	}
	dir := filepath.Join(genDir, "..", "..", pkg)
	paths, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	m := map[string]uint{}
	fset := token.NewFileSet()
	prefix := "Op" + arch
	for _, p := range paths {
		if strings.HasSuffix(p, "_test.go") {
			continue
		}
		src, err := os.ReadFile(p)
		if err != nil || !strings.Contains(string(src), "(v.AuxInt))") {
			continue
		}
		f, err := parser.ParseFile(fset, p, src, 0)
		if err != nil {
			continue
		}
		ast.Inspect(f, func(n ast.Node) bool {
			cc, ok := n.(*ast.CaseClause)
			if !ok {
				return true
			}
			bits := zeroExtendsAuxInt(cc.Body)
			if bits == 0 {
				return true
			}
			for _, e := range cc.List {
				if sel, ok := e.(*ast.SelectorExpr); ok && strings.HasPrefix(sel.Sel.Name, prefix) {
					m[strings.TrimPrefix(sel.Sel.Name, prefix)] = bits
				}
			}
			return true
		})
	}
	return m
}

// zeroExtendsAuxInt returns N if body contains int64(uintN(v.AuxInt))
// for N < 64, and 0 otherwise.
func zeroExtendsAuxInt(body []ast.Stmt) uint {
	var bits uint
	for _, s := range body {
		ast.Inspect(s, func(n ast.Node) bool {
			outer, ok := n.(*ast.CallExpr)
			if !ok || !isIdent(outer.Fun, "int64") || len(outer.Args) != 1 {
				return true
			}
			inner, ok := outer.Args[0].(*ast.CallExpr)
			if !ok || len(inner.Args) != 1 {
				return true
			}
			sel, ok := inner.Args[0].(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "AuxInt" || !isIdent(sel.X, "v") {
				return true
			}
			for _, n := range []uint{8, 16, 32} {
				if isIdent(inner.Fun, "uint"+strconv.Itoa(int(n))) {
					bits = n
				}
			}
			return true
		})
	}
	return bits
}

func isIdent(e ast.Expr, name string) bool {
	id, ok := e.(*ast.Ident)
	return ok && id.Name == name
}
