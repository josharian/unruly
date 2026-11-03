package simdmaskshape

import (
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
)

// A shape is a SIMD vector or mask type of the simd/archsimd API, such as
// Int32x4 or Mask16x8.
type shape struct {
	Kind  string // "Int", "Uint", "Float", or "Mask"
	Elem  int    // element width in bits
	Lanes int
}

var shapeRE = regexp.MustCompile(`^(Int|Uint|Float|Mask)(\d+)x(\d+)$`)

func parseShape(s string) (shape, bool) {
	m := shapeRE.FindStringSubmatch(s)
	if m == nil {
		return shape{}, false
	}
	e, _ := strconv.Atoi(m[2])
	n, _ := strconv.Atoi(m[3])
	return shape{m[1], e, n}, true
}

func (s shape) Bits() int { return s.Elem * s.Lanes }

func (s shape) String() string { return s.Kind + strconv.Itoa(s.Elem) + "x" + strconv.Itoa(s.Lanes) }

// A goSig is the signature of a simd/archsimd method that the compiler
// intrinsifies as a generic SSA op.
type goSig struct {
	Method string   // e.g. "Int32x4.Add"
	Args   []string // Go argument types: the receiver, then the parameters
	Result string   // the first result type
	// Perm maps the generic op's arguments to Go arguments:
	// SSA arg i is Go argument Perm[i]. It is nil if unknown.
	Perm []int
}

// goArg returns the Go type of the generic op's SSA argument i, or "".
func (g *goSig) goArg(i int) string {
	if g.Perm == nil || i >= len(g.Perm) || g.Perm[i] >= len(g.Args) {
		return ""
	}
	return g.Args[g.Perm[i]]
}

// loadGoAPI returns the archsimd signatures of the generic SIMD ops
// that cmd/compile intrinsifies for arch (as named in sys, e.g. "AMD64"),
// keyed by generic op name. Sources: the intrinsic tables in
// cmd/compile/internal/ssagen (addF(simdPackage, "T.M", builder(ssa.OpX, ...), sys.AMD64)),
// the builders' argument orders in ssagen/intrinsics.go, and the method
// declarations of simd/archsimd (or simd, in older trees) for amd64.
//
// It returns nil if the tree has no such sources.
func loadGoAPI(genDir, arch string) map[string][]*goSig {
	src := filepath.Join(genDir, "..", "..", "..", "..", "..")
	ssagen := filepath.Join(src, "cmd", "compile", "internal", "ssagen")
	perms := builderPerms(filepath.Join(ssagen, "intrinsics.go"))
	pkgDir := filepath.Join(src, "simd", "archsimd")
	if _, err := os.Stat(pkgDir); err != nil {
		pkgDir = filepath.Join(src, "simd")
	}
	methods := archsimdMethods(pkgDir, strings.ToLower(arch))
	if len(methods) == 0 {
		return nil
	}
	files, _ := filepath.Glob(filepath.Join(ssagen, "simd*intrinsics*.go"))
	api := map[string][]*goSig{}
	for _, p := range files {
		b, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		for _, line := range strings.Split(string(b), "\n") {
			if !strings.Contains(line, "sys."+arch+")") && !strings.Contains(line, "sys."+arch+",") {
				continue
			}
			m := intrinsicRE.FindStringSubmatch(line)
			if m == nil {
				continue
			}
			recvMethod, builder, op := m[1], m[2], m[3]
			sig, ok := methods[recvMethod]
			if !ok {
				continue
			}
			s := *sig
			s.Perm = perms[builder]
			api[op] = append(api[op], &s)
		}
	}
	return api
}

var intrinsicRE = regexp.MustCompile(`addF\(simdPackage,\s*"(\w+\.\w+)",\s*(\w+)\((?:\w+\.)?Op(\w+)`)

// builderPerms parses the opLen* intrinsic builders in ssagen/intrinsics.go
// and returns, for each, the Go argument index of each SSA argument of the
// value it creates (from its s.newValueN(op, t, [aux,] args[i]...) call).
func builderPerms(path string) map[string][]int {
	perms := map[string][]int{}
	f, err := parser.ParseFile(token.NewFileSet(), path, nil, 0)
	if err != nil {
		return perms
	}
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Recv != nil || !strings.HasPrefix(fd.Name.Name, "opLen") || fd.Body == nil {
			continue
		}
		var perm []int
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			if perm != nil {
				return false
			}
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || !strings.HasPrefix(sel.Sel.Name, "newValue") {
				return true
			}
			p := []int{}
			for _, a := range call.Args {
				ix, ok := a.(*ast.IndexExpr)
				if !ok {
					continue
				}
				if id, ok := ix.X.(*ast.Ident); !ok || id.Name != "args" {
					continue
				}
				lit, ok := ix.Index.(*ast.BasicLit)
				if !ok {
					continue
				}
				i, err := strconv.Atoi(lit.Value)
				if err != nil {
					continue
				}
				p = append(p, i)
			}
			perm = p
			return false
		})
		if perm != nil {
			perms[fd.Name.Name] = perm
		}
	}
	return perms
}

// archsimdMethods returns the methods declared in the simd package in dir
// for goarch, keyed by "Recv.Method".
func archsimdMethods(dir, goarch string) map[string]*goSig {
	ctxt := build.Default
	ctxt.GOOS = "linux"
	ctxt.GOARCH = goarch
	ctxt.BuildTags = []string{"goexperiment.simd"}
	ctxt.CgoEnabled = false
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil
	}
	methods := map[string]*goSig{}
	fset := token.NewFileSet()
	for _, e := range entries {
		name := e.Name()
		if e.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			continue
		}
		if ok, err := ctxt.MatchFile(dir, name); err != nil || !ok {
			continue
		}
		f, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, parser.SkipObjectResolution)
		if err != nil {
			continue
		}
		for _, d := range f.Decls {
			fd, ok := d.(*ast.FuncDecl)
			if !ok || fd.Recv == nil || len(fd.Recv.List) != 1 || fd.Type.Results == nil {
				continue
			}
			recv := typeName(fd.Recv.List[0].Type)
			if recv == "" {
				continue
			}
			args := []string{recv}
			for _, p := range fd.Type.Params.List {
				n := max(1, len(p.Names))
				for range n {
					args = append(args, typeName(p.Type))
				}
			}
			methods[recv+"."+fd.Name.Name] = &goSig{
				Method: recv + "." + fd.Name.Name,
				Args:   args,
				Result: typeName(fd.Type.Results.List[0].Type),
			}
		}
	}
	return methods
}

func typeName(e ast.Expr) string {
	switch e := e.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.StarExpr:
		return typeName(e.X)
	}
	return ""
}
