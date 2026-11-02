// Package typecheck gives Go types to the Go expressions in rules:
// conditions, the contents of <type>, [auxint], and {aux}, result leaves,
// {code} results, and @block placements.
//
// It works the way rulegen's output does. For each rule, it generates a
// function that declares the rule's variables exactly as rulegen's generated
// code does (an auxint variable on a MOVLload gets the type returned by
// auxIntToInt32, a value variable is a *Value, a type variable a
// *types.Type, ...) and uses each expression in the context rulegen puts it
// in (a result [auxint] is passed to the op's xxxToAuxInt function, a
// condition is a boolean, ...). It type-checks these functions as part of
// the package that contains rulegen's generated code for the rule set, using
// the source of the Go tree that the op tables came from, so helpers like
// is32Bit, config fields, and math/bits have their real signatures.
package typecheck

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/build"
	"go/token"
	"go/types"
	"io"
	"os"
	"path/filepath"
	"sync"

	"github.com/josharian/unruly/rules"
)

// Field identifies an expression within an s-expression.
type Field uint8

const (
	Type   Field = iota // <type>
	AuxInt              // [auxint]
	Aux                 // {aux}
	Name                // the node's name: a match variable (a leaf, or x in x:(...)),
	//                     a result leaf's Go expression, or a result's x:(...) name
)

// Result holds the type information for one rule set.
type Result struct {
	Fset *token.FileSet
	Pkg  *types.Package // the package of the generated rewrite code
	Info *types.Info
	// Errors are type errors not attributable to a single rule.
	Errors []error

	rules map[*rules.Rule]*Rule
}

// Rule returns the type information for r, or nil if r is not in the set.
func (res *Result) Rule(r *rules.Rule) *Rule { return res.rules[r] }

// Rule holds the typed expressions of one rule.
// Use the Result's Info to get their types.
type Rule struct {
	// Vars are the variables bound by the match, and the names of
	// result sub-expressions, by name.
	Vars map[string]*types.Var

	Cond      ast.Expr // nil if none
	Code      ast.Expr // the {code} result, or nil
	Placement ast.Expr // the @block expression, or nil

	// Errors are type errors in the rule's expressions, as they would be
	// reported when compiling rulegen's output, such as a constant that
	// overflows its auxint type.
	Errors []error

	exprs map[exprKey]ast.Expr
}

type exprKey struct {
	node  any // *rules.Value or *rules.Block
	field Field
}

// Expr returns the expression for field f of node, which must be a
// *rules.Value or *rules.Block of the rule, or nil if there is none.
// For a match variable, it is the identifier, whose type is
// Info.TypeOf(expr). For a non-variable match field like [0], it is the
// expression compared against.
func (r *Rule) Expr(node any, f Field) ast.Expr {
	return r.exprs[exprKey{node, f}]
}

var cache sync.Map // *rules.RuleSet -> *entry

type entry struct {
	once sync.Once
	res  *Result
	err  error
}

// Check type-checks the rules of set. Results are cached per set.
//
// It needs the Go source tree that set's op tables came from (a Go root, or
// a revision extracted with its src directory), and rulegen's generated
// rewrite code for the set in that tree, which locates the package and the
// declarations that generated code uses.
func Check(set *rules.RuleSet) (*Result, error) {
	e, _ := cache.LoadOrStore(set, new(entry))
	ent := e.(*entry)
	ent.once.Do(func() { ent.res, ent.err = check(set) })
	return ent.res, ent.err
}

var envs struct {
	sync.Mutex
	m map[string]*env
}

// env is the type-checking environment for one Go tree.
type env struct {
	sync.Mutex
	root string
	fset *token.FileSet
	imp  *srcImporter
	pkgs map[string]*pkgInfo // by directory
}

func envFor(root string) *env {
	envs.Lock()
	defer envs.Unlock()
	if envs.m == nil {
		envs.m = make(map[string]*env)
	}
	if e := envs.m[root]; e != nil {
		return e
	}
	fset := token.NewFileSet()
	e := &env{root: root, fset: fset, imp: newSrcImporter(root, fset), pkgs: make(map[string]*pkgInfo)}
	envs.m[root] = e
	return e
}

// rootOf returns the Go root containing genDir (.../src/cmd/compile/internal/ssa/_gen).
func rootOf(genDir string) (string, error) {
	ssaDir := filepath.Dir(genDir)
	root := ssaDir
	for range 5 {
		root = filepath.Dir(root)
	}
	if filepath.Join(root, "src", "cmd", "compile", "internal", "ssa") != ssaDir {
		return "", fmt.Errorf("%s is not inside a Go source tree", genDir)
	}
	if _, err := os.Stat(filepath.Join(root, "src", "go", "build")); err != nil {
		return "", fmt.Errorf("%s has no Go source tree around it (for a revision, extract all of src)", genDir)
	}
	return root, nil
}

func check(set *rules.RuleSet) (*Result, error) {
	root, err := rootOf(set.Arch.Tables().Dir)
	if err != nil {
		return nil, err
	}
	e := envFor(root)
	e.Lock()
	defer e.Unlock()

	ssaDir := filepath.Join(root, "src", "cmd", "compile", "internal", "ssa")
	genFile, err := generatedFile(ssaDir, set.Name())
	if err != nil {
		return nil, err
	}
	pi, err := e.pkg(filepath.Dir(genFile))
	if err != nil {
		return nil, err
	}
	decls, err := e.generatedDecls(ssaDir, genFile)
	if err != nil {
		return nil, err
	}

	g := &generator{decls: decls, pkg: pi.types, imp: e.imp}
	src := g.file(pi.name, set)
	synthName := filepath.Join(filepath.Dir(genFile), "zz_unruly_rules_"+set.Name()+".go")
	f, err := parseSource(e.fset, synthName, src)
	if err != nil {
		return nil, fmt.Errorf("internal error: generated code does not parse: %v", err)
	}

	res := &Result{
		Fset: e.fset,
		Info: &types.Info{
			Types: make(map[ast.Expr]types.TypeAndValue),
			Defs:  make(map[*ast.Ident]types.Object),
			Uses:  make(map[*ast.Ident]types.Object),
		},
		rules: make(map[*rules.Rule]*Rule),
	}
	var typeErrs []types.Error
	conf := types.Config{
		Importer:    e.imp,
		FakeImportC: true,
		Error: func(err error) {
			var terr types.Error
			if errors.As(err, &terr) {
				typeErrs = append(typeErrs, terr)
			}
		},
	}
	pkg := types.NewPackage(pi.path, pi.name)
	files := append(pi.files[:len(pi.files):len(pi.files)], f)
	types.NewChecker(&conf, e.fset, pkg, res.Info).Files(files)
	res.Pkg = pkg

	g.attach(res, f, e.fset, typeErrs)
	return res, nil
}

// generatedFile finds rulegen's output for the named rule set.
func generatedFile(ssaDir, name string) (string, error) {
	base := "rewrite" + name + ".go"
	if p := filepath.Join(ssaDir, base); exists(p) {
		return p, nil
	}
	matches, _ := filepath.Glob(filepath.Join(ssaDir, "rewrite", "*", base))
	if len(matches) == 1 {
		return matches[0], nil
	}
	return "", fmt.Errorf("no generated rewrite code %s in %s", base, ssaDir)
}

// packageName returns the name of the package in dir.
func packageName(dir string) (string, error) {
	bp, err := build.ImportDir(dir, build.ImportComment)
	if bp == nil || bp.Name == "" {
		return "", fmt.Errorf("no package in %s: %v", dir, err)
	}
	return bp.Name, nil
}

// isGeneratedRewrite reports whether file is rulegen output.
func isGeneratedRewrite(file string) bool {
	f, err := os.Open(file)
	if err != nil {
		return false
	}
	defer f.Close()
	buf := make([]byte, 128)
	n, _ := io.ReadFull(f, buf)
	line, _, _ := bytes.Cut(buf[:n], []byte("\n"))
	return bytes.HasPrefix(line, []byte("// Code generated from ")) && bytes.Contains(line, []byte(".rules"))
}

func exists(p string) bool {
	_, err := os.Stat(p)
	return err == nil
}

type pkgInfo struct {
	path, name string
	files      []*ast.File // function bodies removed
	types      *types.Package
}

// pkg loads the package in dir, without function bodies or rulegen's
// generated code, which rules can't refer to.
func (e *env) pkg(dir string) (*pkgInfo, error) {
	if pi := e.pkgs[dir]; pi != nil {
		return pi, nil
	}
	files, err := e.imp.parseDirFilter(dir, false, isGeneratedRewrite)
	if err != nil {
		return nil, err
	}
	name, err := packageName(dir)
	if err != nil {
		return nil, err
	}
	for _, f := range files {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				d.Body = nil
			case *ast.GenDecl:
				// Empty large tables like opcodeTable, which
				// are expensive to check and irrelevant to rules.
				for _, spec := range d.Specs {
					vs, ok := spec.(*ast.ValueSpec)
					if !ok {
						continue
					}
					for _, x := range vs.Values {
						if cl, ok := x.(*ast.CompositeLit); ok && cl.Type != nil && len(cl.Elts) > 100 {
							cl.Elts = nil
						}
					}
				}
			}
		}
	}
	rel, err := filepath.Rel(filepath.Join(e.root, "src"), dir)
	if err != nil {
		return nil, err
	}
	pi := &pkgInfo{path: filepath.ToSlash(rel), name: name, files: files}
	conf := types.Config{Importer: e.imp, FakeImportC: true, Error: func(error) {}}
	pi.types = types.NewPackage(pi.path, pi.name)
	types.NewChecker(&conf, e.fset, pi.types, nil).Files(files)
	e.pkgs[dir] = pi
	return pi, nil
}
