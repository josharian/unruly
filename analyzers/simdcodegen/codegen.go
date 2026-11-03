package simdcodegen

import (
	"go/ast"
	"go/parser"
	"go/token"
	"maps"
	"path/filepath"
	"strconv"
	"strings"
)

// A codegen is the parsed codegen package of one arch, such as
// cmd/compile/internal/amd64.
type codegen struct {
	fset  *token.FileSet
	funcs map[string]*ast.FuncDecl // package-level functions

	// cases maps each op name (without the "Op<Arch>" prefix) to the case
	// clauses of switches on v.Op that list it, and simdCases to those in
	// SIMD dispatch functions (in simdssa*.go files).
	cases     map[string][]*clause
	simdCases map[string][]*clause
	// zeroing is the set of ops that the codegen gives AVX-512 zeroing-masking:
	// those in a switch clause that calls ParseSuffix(p, "Z").
	zeroing map[string]token.Position

	memo map[memoKey]*facts
}

type clause struct {
	cc    *ast.CaseClause
	value string // the name of the *ssa.Value switched on, usually v
	pos   token.Position
}

type memoKey struct {
	fn    string
	param int
}

// loadCodegen parses the Go files of dir, the codegen package of arch.
// It returns nil if there are none.
func loadCodegen(dir, arch string) *codegen {
	paths, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	cg := &codegen{
		fset:      token.NewFileSet(),
		funcs:     make(map[string]*ast.FuncDecl),
		cases:     make(map[string][]*clause),
		simdCases: make(map[string][]*clause),
		zeroing:   make(map[string]token.Position),
		memo:      make(map[memoKey]*facts),
	}
	var files []*ast.File
	for _, path := range paths {
		if strings.HasSuffix(path, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(cg.fset, path, nil, parser.SkipObjectResolution)
		if err != nil {
			continue
		}
		files = append(files, f)
		for _, d := range f.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Recv == nil && fd.Body != nil {
				cg.funcs[fd.Name.Name] = fd
			}
		}
	}
	if len(files) == 0 {
		return nil
	}
	prefix := "Op" + arch
	for _, f := range files {
		simd := strings.HasPrefix(filepath.Base(cg.fset.Position(f.Pos()).Filename), "simdssa")
		ast.Inspect(f, func(n ast.Node) bool {
			sw, ok := n.(*ast.SwitchStmt)
			if !ok {
				return true
			}
			value := opSwitchValue(sw)
			if value == "" {
				return true
			}
			for _, s := range sw.Body.List {
				cc := s.(*ast.CaseClause)
				cl := &clause{cc: cc, value: value, pos: cg.fset.Position(cc.Pos())}
				zero := callsParseSuffixZ(cc)
				for _, e := range cc.List {
					sel, ok := e.(*ast.SelectorExpr)
					if !ok {
						continue
					}
					name, ok := strings.CutPrefix(sel.Sel.Name, prefix)
					if !ok {
						continue
					}
					cg.cases[name] = append(cg.cases[name], cl)
					if simd {
						cg.simdCases[name] = append(cg.simdCases[name], cl)
					}
					if zero {
						if _, ok := cg.zeroing[name]; !ok {
							cg.zeroing[name] = cl.pos
						}
					}
				}
			}
			return true
		})
	}
	return cg
}

// opSwitchValue returns v if sw is "switch v.Op", else "".
func opSwitchValue(sw *ast.SwitchStmt) string {
	sel, ok := sw.Tag.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Op" {
		return ""
	}
	id, ok := sel.X.(*ast.Ident)
	if !ok {
		return ""
	}
	return id.Name
}

// callsParseSuffixZ reports whether cc calls x86.ParseSuffix(p, "Z").
func callsParseSuffixZ(cc *ast.CaseClause) bool {
	found := false
	for _, s := range cc.Body {
		ast.Inspect(s, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) != 2 {
				return true
			}
			if sel, ok := call.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "ParseSuffix" {
				if lit, ok := call.Args[1].(*ast.BasicLit); ok && lit.Value == `"Z"` {
					found = true
				}
			}
			return !found
		})
	}
	return found
}

// facts are what codegen does with an *ssa.Value.
type facts struct {
	aux       bool         // reads Aux or AuxInt (directly or via ssagen.AddAux)
	auxVO     bool         // decodes AuxInt as a ValAndOff
	args      map[int]bool // reads v.Args[i]
	allArgs   bool         // uses v.Args other than by constant index
	opaque    bool         // passes v to code not analyzed here
	helpers   []string     // package functions v is passed to
	maxArgIdx int          // largest constant i in v.Args[i], or -1
}

func newFacts() *facts { return &facts{args: make(map[int]bool), maxArgIdx: -1} }

func (f *facts) merge(g *facts) {
	f.aux = f.aux || g.aux
	f.auxVO = f.auxVO || g.auxVO
	f.allArgs = f.allArgs || g.allArgs
	f.opaque = f.opaque || g.opaque
	maps.Copy(f.args, g.args)
	f.maxArgIdx = max(f.maxArgIdx, g.maxArgIdx)
}

// auxFuncs are functions outside the codegen package that read the aux
// fields of the value passed to them.
var auxFuncs = map[string]bool{"AddAux": true, "AddAux2": true}

// clauseFacts returns the facts of a case clause about the switched value.
func (cg *codegen) clauseFacts(cl *clause) *facts {
	f := newFacts()
	for _, s := range cl.cc.Body {
		sf := cg.nodeFacts(s, cl.value, nil)
		f.merge(sf)
		f.helpers = append(f.helpers, sf.helpers...)
	}
	return f
}

// funcFacts returns the facts of the package function fn about its param'th
// parameter.
func (cg *codegen) funcFacts(fn string, param int, stack []memoKey) *facts {
	k := memoKey{fn, param}
	if f, ok := cg.memo[k]; ok {
		return f
	}
	for _, s := range stack {
		if s == k {
			return newFacts() // recursion: assume nothing more
		}
	}
	fd := cg.funcs[fn]
	name := paramName(fd, param)
	f := newFacts()
	if name == "" {
		f.opaque = true
	} else {
		f.merge(cg.nodeFacts(fd.Body, name, append(stack, k)))
	}
	cg.memo[k] = f
	return f
}

func paramName(fd *ast.FuncDecl, param int) string {
	i := 0
	for _, field := range fd.Type.Params.List {
		if len(field.Names) == 0 {
			return ""
		}
		for _, n := range field.Names {
			if i == param {
				return n.Name
			}
			i++
		}
	}
	return ""
}

// nodeFacts returns the facts of the code n about the value named v.
func (cg *codegen) nodeFacts(n ast.Node, v string, stack []memoKey) *facts {
	f := newFacts()
	handled := make(map[*ast.Ident]bool) // uses of v accounted for
	isV := func(e ast.Expr) bool {
		id, ok := e.(*ast.Ident)
		return ok && id.Name == v
	}
	ast.Inspect(n, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.IndexExpr:
			sel, ok := n.X.(*ast.SelectorExpr)
			if !ok || !isV(sel.X) || sel.Sel.Name != "Args" {
				break
			}
			lit, ok := n.Index.(*ast.BasicLit)
			if !ok || lit.Kind != token.INT {
				break
			}
			i, err := strconv.Atoi(lit.Value)
			if err != nil {
				break
			}
			f.args[i] = true
			f.maxArgIdx = max(f.maxArgIdx, i)
			handled[sel.X.(*ast.Ident)] = true
		case *ast.SelectorExpr:
			if !isV(n.X) || handled[n.X.(*ast.Ident)] {
				break
			}
			handled[n.X.(*ast.Ident)] = true
			switch name := n.Sel.Name; {
			case name == "Args":
				f.allArgs = true
			case name == "AuxValAndOff":
				f.aux, f.auxVO = true, true
			case strings.HasPrefix(name, "Aux"):
				f.aux = true
			}
		case *ast.CallExpr:
			for i, a := range n.Args {
				if !isV(a) {
					continue
				}
				handled[a.(*ast.Ident)] = true
				switch fn := n.Fun.(type) {
				case *ast.Ident:
					if cg.funcs[fn.Name] != nil {
						f.helpers = append(f.helpers, fn.Name)
						f.merge(cg.funcFacts(fn.Name, i, stack))
						continue
					}
				case *ast.SelectorExpr:
					if auxFuncs[fn.Sel.Name] {
						f.aux = true
						continue
					}
				}
				f.opaque = true
			}
		case *ast.Ident:
			if n.Name == v && !handled[n] {
				// Some other use of v, such as an assignment.
				f.opaque = true
			}
		}
		return true
	})
	return f
}
