package typecheck

import (
	"errors"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"strings"
)

// srcImporter type-checks packages from the source of a Go tree,
// ignoring function bodies. It resolves import paths the way the go
// command does within GOROOT: cmd packages vendor from src/cmd/vendor,
// std packages from src/vendor.
type srcImporter struct {
	root string // contains src
	fset *token.FileSet
	ctxt build.Context
	pkgs map[string]*types.Package // by directory
	errs map[string]error
}

func newSrcImporter(root string, fset *token.FileSet) *srcImporter {
	ctxt := build.Default
	ctxt.GOROOT = root
	ctxt.GOPATH = ""
	ctxt.GOOS = "linux"
	ctxt.GOARCH = "amd64"
	ctxt.CgoEnabled = false
	ctxt.Compiler = "gc"
	ctxt.BuildTags = nil
	ctxt.ToolTags = nil // all GOEXPERIMENTs off; fine for declarations
	return &srcImporter{
		root: root,
		fset: fset,
		ctxt: ctxt,
		pkgs: make(map[string]*types.Package),
		errs: make(map[string]error),
	}
}

func (imp *srcImporter) Import(path string) (*types.Package, error) {
	return imp.ImportFrom(path, "", 0)
}

func (imp *srcImporter) ImportFrom(path, fromDir string, _ types.ImportMode) (*types.Package, error) {
	if path == "unsafe" {
		return types.Unsafe, nil
	}
	dir := imp.resolve(path, fromDir)
	if pkg := imp.pkgs[dir]; pkg != nil {
		if !pkg.Complete() {
			return nil, fmt.Errorf("import cycle through %s", path)
		}
		return pkg, nil
	}
	if err := imp.errs[dir]; err != nil {
		return nil, err
	}
	pkg, err := imp.load(path, dir)
	if err != nil {
		imp.errs[dir] = err
		return nil, err
	}
	return pkg, nil
}

func (imp *srcImporter) resolve(path, fromDir string) string {
	src := filepath.Join(imp.root, "src")
	if strings.HasPrefix(path, "cmd/") {
		return filepath.Join(src, filepath.FromSlash(path))
	}
	if first, _, _ := strings.Cut(path, "/"); strings.Contains(first, ".") {
		cmdDir := filepath.Join(src, "cmd")
		if fromDir == cmdDir || strings.HasPrefix(fromDir, cmdDir+string(filepath.Separator)) {
			return filepath.Join(cmdDir, "vendor", filepath.FromSlash(path))
		}
		return filepath.Join(src, "vendor", filepath.FromSlash(path))
	}
	return filepath.Join(src, filepath.FromSlash(path))
}

func (imp *srcImporter) load(path, dir string) (*types.Package, error) {
	files, err := imp.parseDir(dir, false)
	if err != nil {
		return nil, fmt.Errorf("importing %s: %v", path, err)
	}
	pkg := types.NewPackage(path, files[0].Name.Name)
	imp.pkgs[dir] = pkg
	conf := types.Config{
		Importer:         imp,
		IgnoreFuncBodies: true,
		FakeImportC:      true,
		Error:            func(error) {}, // tolerate errors in dependencies
	}
	types.NewChecker(&conf, imp.fset, pkg, nil).Files(files)
	pkg.MarkComplete()
	return pkg, nil
}

// parseDir parses the Go files of the package in dir, as selected by build
// constraints. If keepTests, test files of the same package are included.
func (imp *srcImporter) parseDir(dir string, keepTests bool) ([]*ast.File, error) {
	return imp.parseDirFilter(dir, keepTests, nil)
}

// parseDirFilter is like parseDir, but skips files for which skip returns true.
func (imp *srcImporter) parseDirFilter(dir string, keepTests bool, skip func(path string) bool) ([]*ast.File, error) {
	bp, err := imp.ctxt.ImportDir(dir, 0)
	if err != nil {
		var noGo *build.NoGoError
		if !errors.As(err, &noGo) {
			if _, statErr := os.Stat(dir); statErr != nil {
				return nil, statErr
			}
		}
		if bp == nil || len(bp.GoFiles) == 0 {
			return nil, err
		}
	}
	names := bp.GoFiles
	if keepTests {
		names = append(names, bp.TestGoFiles...)
	}
	var files []*ast.File
	for _, name := range names {
		if skip != nil && skip(filepath.Join(dir, name)) {
			continue
		}
		f, err := parser.ParseFile(imp.fset, filepath.Join(dir, name), nil, parser.SkipObjectResolution)
		if err != nil {
			return nil, err
		}
		files = append(files, f)
	}
	if len(files) == 0 && skip == nil {
		return nil, fmt.Errorf("no Go files in %s", dir)
	}
	return files, nil
}
