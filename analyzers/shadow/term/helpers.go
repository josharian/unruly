package term

import (
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// A helper is a function of the ssa package whose body is a single
// return of an expression over its parameters, such as
//
//	func OneBit[T int8 | int16 | int32 | int64](x T) bool {
//		return x&(x-1) == 0 && x != 0
//	}
//
// Conditions call such helpers; with constant arguments, the analyzers
// evaluate them by inlining the body.
type helper struct {
	params []string
	body   string
}

var (
	helpersMu    sync.Mutex
	helpersCache = map[string]map[string]helper{}
)

// loadHelpers returns the helpers of the ssa package that genDir, a _gen
// directory, generates rules for.
func loadHelpers(genDir string) map[string]helper {
	helpersMu.Lock()
	defer helpersMu.Unlock()
	if h, ok := helpersCache[genDir]; ok {
		return h
	}
	h := map[string]helper{}
	helpersCache[genDir] = h
	dir := filepath.Dir(genDir)
	paths, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	fset := token.NewFileSet()
	for _, p := range paths {
		if strings.HasSuffix(p, "_test.go") {
			continue
		}
		src, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		f, err := parser.ParseFile(fset, p, src, 0)
		if err != nil {
			continue
		}
		for _, d := range f.Decls {
			fd, ok := d.(*ast.FuncDecl)
			if !ok || fd.Recv != nil || fd.Body == nil || len(fd.Body.List) != 1 {
				continue
			}
			ret, ok := fd.Body.List[0].(*ast.ReturnStmt)
			if !ok || len(ret.Results) != 1 {
				continue
			}
			var params []string
			for _, field := range fd.Type.Params.List {
				for _, n := range field.Names {
					params = append(params, n.Name)
				}
			}
			body := string(src[fset.Position(ret.Results[0].Pos()).Offset:fset.Position(ret.Results[0].End()).Offset])
			h[fd.Name.Name] = helper{params, Canon(body)}
		}
	}
	return h
}

// UseHelpers lets f evaluate calls of the helpers of the ssa package
// whose rules live in genDir, a _gen directory.
func (f *Facts) UseHelpers(genDir string) {
	f.helpers = loadHelpers(genDir)
}

// eval returns the constant value of c, inlining calls of helpers with
// constant arguments.
func (f *Facts) eval(c string) constant.Value {
	if v := Eval(c); v != nil || len(f.helpers) == 0 {
		return v
	}
	for range 10 {
		next, ok := f.inlineOne(c)
		if !ok {
			return nil
		}
		c = next
		if v := Eval(c); v != nil {
			return v
		}
	}
	return nil
}

// inlineOne inlines one call of a helper with constant arguments in c.
func (f *Facts) inlineOne(c string) (string, bool) {
	x, err := parser.ParseExpr(c)
	if err != nil {
		return "", false
	}
	var out string
	ast.Inspect(x, func(n ast.Node) bool {
		if out != "" {
			return false
		}
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		h, ok := f.helpers[funcName(call.Fun)]
		if !ok || len(h.params) != len(call.Args) {
			return true
		}
		args := map[string]string{}
		for i, a := range call.Args {
			text := format(a)
			if Eval(text) == nil {
				return true
			}
			args[h.params[i]] = text
		}
		body := Subst(h.body, func(name string) (string, bool) {
			a, ok := args[name]
			return a, ok
		})
		// ParseExpr positions are 1-based offsets into c.
		start, end := int(call.Pos())-1, int(call.End())-1
		out = c[:start] + "(" + body + ")" + c[end:]
		return false
	})
	return out, out != ""
}
