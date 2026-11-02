package ops

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/format"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"text/template"
)

// dumpVersion is part of the cache key. Bump it whenever the dump program
// or the JSON it produces changes.
const dumpVersion = "unruly-opdump-2"

// dump builds the _gen package in dir together with a generated main
// function that dumps the registered op tables as JSON.
//
// The _gen package cannot be built as is: it imports golang.org/x/tools
// (vendored in recent trees, absent in extracted historical trees), and its
// main generates code. So dump type-checks the package, deletes every
// top-level function that does not type-check (repeating until none remain),
// replaces main, and runs the result. Op tables are plain data registered by
// init functions, so they survive this pruning intact.
func dump(dir string) ([]byte, error) {
	fset := token.NewFileSet()
	files, err := parseGenDir(fset, dir)
	if err != nil {
		return nil, err
	}
	pkg, err := prune(fset, files)
	if err != nil {
		return nil, fmt.Errorf("pruning %s: %v", dir, err)
	}
	main, err := dumpMain(pkg)
	if err != nil {
		return nil, err
	}

	tmp, err := os.MkdirTemp("", "unruly-opdump-")
	if err != nil {
		return nil, err
	}
	defer os.RemoveAll(tmp)
	for _, f := range files {
		var buf bytes.Buffer
		if err := format.Node(&buf, fset, f); err != nil {
			return nil, err
		}
		name := filepath.Base(fset.File(f.Pos()).Name())
		if err := os.WriteFile(filepath.Join(tmp, name), buf.Bytes(), 0o666); err != nil {
			return nil, err
		}
	}
	if err := os.WriteFile(filepath.Join(tmp, "zz_unruly_dump.go"), main, 0o666); err != nil {
		return nil, err
	}
	lang, err := goLangVersion()
	if err != nil {
		return nil, err
	}
	gomod := fmt.Sprintf("module unrulyopdump\n\ngo %s\n", lang)
	if err := os.WriteFile(filepath.Join(tmp, "go.mod"), []byte(gomod), 0o666); err != nil {
		return nil, err
	}

	out := filepath.Join(tmp, "dump.json")
	cmd := exec.Command("go", "run", ".", out)
	cmd.Dir = tmp
	cmd.Env = append(os.Environ(), "GOWORK=off", "GOFLAGS=", "GOTOOLCHAIN=local", "GO111MODULE=on")
	if b, err := cmd.CombinedOutput(); err != nil {
		return nil, fmt.Errorf("running op dump for %s: %v\n%s", dir, err, b)
	}
	return os.ReadFile(out)
}

// parseGenDir parses the package main files of a _gen directory.
// Comments are dropped, which also drops build constraints
// (older gen directories were marked "//go:build ignore").
func parseGenDir(fset *token.FileSet, dir string) ([]*ast.File, error) {
	names, err := genGoFiles(dir)
	if err != nil {
		return nil, err
	}
	var files []*ast.File
	for _, name := range names {
		f, err := parser.ParseFile(fset, filepath.Join(dir, name), nil, parser.SkipObjectResolution)
		if err != nil {
			return nil, err
		}
		if f.Name.Name != "main" {
			continue
		}
		files = append(files, f)
	}
	if len(files) == 0 {
		return nil, fmt.Errorf("no package main Go files in %s", dir)
	}
	return files, nil
}

// genGoFiles returns the sorted names of the non-test Go files in dir.
func genGoFiles(dir string) ([]string, error) {
	ents, err := os.ReadDir(dir)
	if err != nil {
		return nil, err
	}
	var names []string
	for _, e := range ents {
		name := e.Name()
		if e.Type().IsRegular() && strings.HasSuffix(name, ".go") && !strings.HasSuffix(name, "_test.go") {
			names = append(names, name)
		}
	}
	slices.Sort(names)
	return names, nil
}

// prune deletes func main and every top-level function or import that
// fails to type-check, until the package type-checks. It returns the
// resulting package.
func prune(fset *token.FileSet, files []*ast.File) (*types.Package, error) {
	for _, f := range files {
		f.Decls = slices.DeleteFunc(f.Decls, func(d ast.Decl) bool {
			fd, ok := d.(*ast.FuncDecl)
			return ok && fd.Recv == nil && fd.Name.Name == "main"
		})
	}
	imp := stdImporter{importer.ForCompiler(fset, "gc", nil)}
	for range 100 {
		var errs []types.Error
		conf := types.Config{
			Importer: imp,
			Error: func(err error) {
				var terr types.Error
				if errors.As(err, &terr) {
					errs = append(errs, terr)
				}
			},
		}
		pkg, _ := conf.Check("main", fset, files, nil)
		if len(errs) == 0 {
			return pkg, nil
		}
		for _, terr := range errs {
			if err := deleteEnclosing(files, terr); err != nil {
				return nil, err
			}
		}
	}
	return nil, errors.New("type errors persist after pruning")
}

// stdImporter imports only standard library packages, so that the build
// in a temporary module doesn't depend on whether the importer happens to
// find a non-std package (such as x/tools) some other way.
type stdImporter struct{ types.Importer }

func (imp stdImporter) Import(path string) (*types.Package, error) {
	first, _, _ := strings.Cut(path, "/")
	if strings.Contains(first, ".") {
		return nil, fmt.Errorf("not a standard library package: %s", path)
	}
	return imp.Importer.Import(path)
}

// deleteEnclosing deletes the top-level function or import spec containing
// the position of terr. It is an error for terr to lie elsewhere.
func deleteEnclosing(files []*ast.File, terr types.Error) error {
	for _, f := range files {
		if terr.Pos < f.Pos() || terr.Pos > f.End() {
			continue
		}
		for i, d := range f.Decls {
			if terr.Pos < d.Pos() || terr.Pos > d.End() {
				continue
			}
			switch d := d.(type) {
			case *ast.FuncDecl:
				if d.Recv == nil && d.Name.Name == "init" {
					return fmt.Errorf("init function does not type-check: %v", terr)
				}
				f.Decls = slices.Delete(f.Decls, i, i+1)
				return nil
			case *ast.GenDecl:
				if d.Tok != token.IMPORT {
					break
				}
				d.Specs = slices.DeleteFunc(d.Specs, func(s ast.Spec) bool {
					return terr.Pos >= s.Pos() && terr.Pos <= s.End()
				})
				if len(d.Specs) == 0 {
					f.Decls = slices.Delete(f.Decls, i, i+1)
				}
				return nil
			}
			return fmt.Errorf("declaration does not type-check: %v", terr)
		}
		// Already deleted by an earlier error in this round.
		return nil
	}
	return fmt.Errorf("unexpected type error: %v", terr)
}

// goLangVersion returns the language version (e.g. "1.27")
// of the go command on PATH.
func goLangVersion() (string, error) {
	out, err := exec.Command("go", "env", "GOVERSION").Output()
	if err != nil {
		return "", fmt.Errorf("go env GOVERSION: %v", err)
	}
	v := strings.TrimPrefix(strings.TrimSpace(string(out)), "go")
	// Strip patch and prerelease: 1.27.3 -> 1.27, 1.28-devel_abc -> 1.28.
	v, _, _ = strings.Cut(v, "-")
	v, _, _ = strings.Cut(v, " ")
	parts := strings.SplitN(v, ".", 3)
	if len(parts) < 2 {
		return "", fmt.Errorf("unrecognized GOVERSION %q", out)
	}
	minor, _, _ := strings.Cut(parts[1], "rc")
	minor, _, _ = strings.Cut(minor, "beta")
	return parts[0] + "." + minor, nil
}

// dumpConfig records which optional declarations the _gen package has,
// so that the generated main uses only what exists in this revision.
type dumpConfig struct {
	GenericInit   bool // func genericInit()
	GenericOps    bool // var genericOps []opData
	GenericBlocks bool // var genericBlocks []blockData
	ReservedNames bool // var reservedNames map[string]bool
	OpAuxType     bool // func (opData) auxType() string
	OpAuxIntType  bool // func (opData) auxIntType() string
	OpHasAux      bool // func opHasAux(opData) bool
	OpHasAuxInt   bool // func opHasAuxInt(opData) bool
	BlockAuxType  bool // func (blockData) auxType() string
	BlockAuxInt   bool // func (blockData) auxIntType() string
	ArchOpsField  bool // arch.ops
	ArchBlocksFld bool // arch.blocks
}

func dumpMain(pkg *types.Package) ([]byte, error) {
	scope := pkg.Scope()
	if _, ok := scope.Lookup("archs").(*types.Var); !ok {
		return nil, errors.New("_gen package has no archs variable")
	}
	opData := scope.Lookup("opData")
	blockData := scope.Lookup("blockData")
	arch := scope.Lookup("arch")
	if opData == nil || blockData == nil || arch == nil {
		return nil, errors.New("_gen package lacks opData, blockData, or arch")
	}
	isVar := func(name string) bool {
		_, ok := scope.Lookup(name).(*types.Var)
		return ok
	}
	hasFunc := func(name string, params int, result string) bool {
		fn, ok := scope.Lookup(name).(*types.Func)
		if !ok {
			return false
		}
		return sigMatches(fn.Type().(*types.Signature), params, result)
	}
	hasMethod := func(typ types.Object, name, result string) bool {
		obj, _, _ := types.LookupFieldOrMethod(typ.Type(), false, pkg, name)
		fn, ok := obj.(*types.Func)
		return ok && sigMatches(fn.Type().(*types.Signature), 0, result)
	}
	hasField := func(typ types.Object, name string) bool {
		obj, _, _ := types.LookupFieldOrMethod(typ.Type(), false, pkg, name)
		_, ok := obj.(*types.Var)
		return ok
	}
	cfg := dumpConfig{
		GenericInit:   hasFunc("genericInit", 0, ""),
		GenericOps:    isVar("genericOps"),
		GenericBlocks: isVar("genericBlocks"),
		ReservedNames: isVar("reservedNames"),
		OpAuxType:     hasMethod(opData, "auxType", "string"),
		OpAuxIntType:  hasMethod(opData, "auxIntType", "string"),
		OpHasAux:      hasFunc("opHasAux", 1, "bool"),
		OpHasAuxInt:   hasFunc("opHasAuxInt", 1, "bool"),
		BlockAuxType:  hasMethod(blockData, "auxType", "string"),
		BlockAuxInt:   hasMethod(blockData, "auxIntType", "string"),
		ArchOpsField:  hasField(arch, "ops"),
		ArchBlocksFld: hasField(arch, "blocks"),
	}
	var buf bytes.Buffer
	if err := dumpTemplate.Execute(&buf, cfg); err != nil {
		return nil, err
	}
	return format.Source(buf.Bytes())
}

func sigMatches(sig *types.Signature, params int, result string) bool {
	if sig.Params().Len() != params {
		return false
	}
	if result == "" {
		return sig.Results().Len() == 0
	}
	return sig.Results().Len() == 1 && sig.Results().At(0).Type().String() == result
}

var dumpTemplate = template.Must(template.New("dump").Parse(`// Code generated by unruly. DO NOT EDIT.

package main

import (
	unrulyjson "encoding/json"
	unrulyos "os"
	unrulyreflect "reflect"
)

func main() {
	{{if .GenericInit}}genericInit(){{end}}
	out := map[string]any{
		"archs": unrulyDump(unrulyreflect.ValueOf(archs)),
	}
	{{- if .GenericOps}}
	out["genericOps"] = unrulyDump(unrulyreflect.ValueOf(genericOps))
	out["genericOpExtra"] = unrulyOpExtras(genericOps)
	{{- end}}
	{{- if .GenericBlocks}}
	out["genericBlocks"] = unrulyDump(unrulyreflect.ValueOf(genericBlocks))
	out["genericBlockExtra"] = unrulyBlockExtras(genericBlocks)
	{{- end}}
	{{- if .ReservedNames}}
	out["reservedNames"] = unrulyDump(unrulyreflect.ValueOf(reservedNames))
	{{- end}}
	{{- if .ArchOpsField}}
	var opExtra [][]map[string]any
	for _, a := range archs {
		opExtra = append(opExtra, unrulyOpExtras(a.ops))
	}
	out["opExtra"] = opExtra
	{{- end}}
	{{- if .ArchBlocksFld}}
	var blockExtra [][]map[string]any
	for _, a := range archs {
		blockExtra = append(blockExtra, unrulyBlockExtras(a.blocks))
	}
	out["blockExtra"] = blockExtra
	{{- end}}
	b, err := unrulyjson.Marshal(out)
	if err != nil {
		panic(err)
	}
	if err := unrulyos.WriteFile(unrulyos.Args[1], b, 0o666); err != nil {
		panic(err)
	}
}

// unrulyOpExtras records rulegen's derived per-op aux information.
func unrulyOpExtras(ops []opData) []map[string]any {
	var r []map[string]any
	for _, op := range ops {
		m := map[string]any{}
		{{- if .OpAuxType}}
		m["auxType"] = op.auxType()
		{{- end}}
		{{- if .OpAuxIntType}}
		m["auxIntType"] = op.auxIntType()
		{{- end}}
		{{- if .OpHasAux}}
		m["hasAux"] = opHasAux(op)
		{{- end}}
		{{- if .OpHasAuxInt}}
		m["hasAuxInt"] = opHasAuxInt(op)
		{{- end}}
		_ = op
		r = append(r, m)
	}
	return r
}

// unrulyBlockExtras records rulegen's derived per-block aux information.
func unrulyBlockExtras(blocks []blockData) []map[string]any {
	var r []map[string]any
	for _, b := range blocks {
		m := map[string]any{}
		{{- if .BlockAuxType}}
		m["auxType"] = b.auxType()
		{{- end}}
		{{- if .BlockAuxInt}}
		m["auxIntType"] = b.auxIntType()
		{{- end}}
		_ = b
		r = append(r, m)
	}
	return r
}

// unrulyDump converts v to JSON-compatible data by reflection,
// reading unexported fields and flattening embedded structs.
func unrulyDump(v unrulyreflect.Value) any {
	switch v.Kind() {
	case unrulyreflect.Bool:
		return v.Bool()
	case unrulyreflect.Int, unrulyreflect.Int8, unrulyreflect.Int16, unrulyreflect.Int32, unrulyreflect.Int64:
		return v.Int()
	case unrulyreflect.Uint, unrulyreflect.Uint8, unrulyreflect.Uint16, unrulyreflect.Uint32, unrulyreflect.Uint64, unrulyreflect.Uintptr:
		return v.Uint()
	case unrulyreflect.Float32, unrulyreflect.Float64:
		return v.Float()
	case unrulyreflect.String:
		return v.String()
	case unrulyreflect.Slice, unrulyreflect.Array:
		if v.Kind() == unrulyreflect.Slice && v.IsNil() {
			return nil
		}
		l := make([]any, v.Len())
		for i := range l {
			l[i] = unrulyDump(v.Index(i))
		}
		return l
	case unrulyreflect.Map:
		if v.IsNil() {
			return nil
		}
		m := map[string]any{}
		iter := v.MapRange()
		for iter.Next() {
			k := iter.Key()
			if k.Kind() != unrulyreflect.String {
				return nil
			}
			m[k.String()] = unrulyDump(iter.Value())
		}
		return m
	case unrulyreflect.Pointer, unrulyreflect.Interface:
		if v.IsNil() {
			return nil
		}
		return unrulyDump(v.Elem())
	case unrulyreflect.Struct:
		m := map[string]any{}
		unrulyDumpFields(v, m)
		return m
	}
	return nil // funcs, chans, etc.
}

func unrulyDumpFields(v unrulyreflect.Value, m map[string]any) {
	t := v.Type()
	for i := 0; i < t.NumField(); i++ {
		f := t.Field(i)
		if f.Anonymous && f.Type.Kind() == unrulyreflect.Struct {
			unrulyDumpFields(v.Field(i), m)
			continue
		}
		m[f.Name] = unrulyDump(v.Field(i))
	}
}
`))
