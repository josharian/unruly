package facts

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"math/big"
	"os"
	"strings"
	"sync"
)

// Helpers called by rules, such as is32Bit, log64, and ValAndOff.Val, are
// understood by inlining their definitions from the Go tree, so that facts
// follows the tree's own semantics for them, at any revision.
//
// A function (or method) is inlined if its body is a single return
// statement, optionally preceded by definitions x := e. Its body is
// type-checked in its package, and its parameters stand for the call's
// arguments.

// maxDepth limits nested inlining.
const maxDepth = 8

type inlined struct {
	info   *types.Info
	params []types.Object // receiver, then parameters
	locals []local
	ret    ast.Expr
}

type local struct {
	obj types.Object
	e   ast.Expr
}

type inlineKey struct {
	fn    *types.Func
	targs string
}

var inlines struct {
	sync.Mutex
	m     map[inlineKey]*inlined // nil if not inlinable
	files map[string]*parsedFile
}

type parsedFile struct {
	fset *token.FileSet
	src  []byte
	file *ast.File
}

// callee returns the function or method that call calls, its receiver
// expression if a method, and the type arguments of a generic function.
func (f *Facts) callee(call *ast.CallExpr, en *env) (fn *types.Func, recv ast.Expr, targs []types.Type, ok bool) {
	fun := unparen(call.Fun)
	var explicit []ast.Expr
	switch x := fun.(type) {
	case *ast.IndexExpr:
		fun, explicit = x.X, []ast.Expr{x.Index}
	case *ast.IndexListExpr:
		fun, explicit = x.X, x.Indices
	}
	var id *ast.Ident
	switch x := fun.(type) {
	case *ast.Ident:
		id = x
	case *ast.SelectorExpr:
		id = x.Sel
		if xid, ok := x.X.(*ast.Ident); !ok || f.obj(xid, en) == nil || !isPkgName(f.obj(xid, en)) {
			recv = x.X
		}
	default:
		return nil, nil, nil, false
	}
	fn, ok = f.obj(id, en).(*types.Func)
	if !ok || call.Ellipsis.IsValid() {
		return nil, nil, nil, false
	}
	sig := fn.Signature()
	if (recv != nil) != (sig.Recv() != nil) || sig.Variadic() || sig.Params().Len() != len(call.Args) {
		return nil, nil, nil, false
	}
	if recv != nil && !types.Identical(sig.Recv().Type(), f.typeOf(recv, en)) {
		// Not a direct call on recv: an embedded method, or an
		// implicit & or *. Its receiver is not recv itself.
		return nil, nil, nil, false
	}
	if tps := sig.TypeParams(); tps.Len() > 0 {
		targs = make([]types.Type, tps.Len())
		for i, x := range explicit {
			if tv, ok := en.info.Types[x]; ok && tv.IsType() && i < len(targs) {
				targs[i] = tv.Type
			}
		}
		for i := range sig.Params().Len() {
			tp, ok := sig.Params().At(i).Type().(*types.TypeParam)
			if !ok || targs[tp.Index()] != nil {
				continue
			}
			targs[tp.Index()] = types.Default(f.typeOf(call.Args[i], en))
		}
		for _, t := range targs {
			if b, ok := t.(*types.Basic); !ok || b.Info()&types.IsUntyped != 0 {
				return nil, nil, nil, false
			}
		}
	}
	return fn, recv, targs, true
}

func isPkgName(obj types.Object) bool {
	_, ok := obj.(*types.PkgName)
	return ok
}

// inline returns the return expression of the helper that call calls,
// and the environment that binds its parameters to call's arguments.
func (f *Facts) inline(call *ast.CallExpr, en *env) (ast.Expr, *env, bool) {
	if en.depth >= maxDepth {
		return nil, nil, false
	}
	fn, recv, targs, ok := f.callee(call, en)
	if !ok || fn.Pkg() == nil || !strings.HasPrefix(fn.Pkg().Path(), "cmd/") {
		return nil, nil, false
	}
	inl := inlineFunc(f.res.Fset, fn, targs)
	if inl == nil {
		return nil, nil, false
	}
	args := call.Args
	if recv != nil {
		args = append([]ast.Expr{recv}, args...)
	}
	ben := &env{info: inl.info, bind: make(map[types.Object]binding), depth: en.depth + 1}
	for i, p := range inl.params {
		ben.bind[p] = binding{args[i], en}
	}
	for _, l := range inl.locals {
		ben.bind[l.obj] = binding{l.e, ben}
	}
	return inl.ret, ben, true
}

func inlineFunc(fset *token.FileSet, fn *types.Func, targs []types.Type) *inlined {
	var ts []string
	for _, t := range targs {
		ts = append(ts, t.String())
	}
	k := inlineKey{fn, strings.Join(ts, ",")}
	inlines.Lock()
	defer inlines.Unlock()
	if inl, ok := inlines.m[k]; ok {
		return inl
	}
	if inlines.m == nil {
		inlines.m = make(map[inlineKey]*inlined)
		inlines.files = make(map[string]*parsedFile)
	}
	inl := buildInline(fset, fn, targs)
	inlines.m[k] = inl
	return inl
}

func buildInline(fset *token.FileSet, fn *types.Func, targs []types.Type) *inlined {
	pos := fset.Position(fn.Pos())
	pf := parseFile(pos.Filename)
	if pf == nil {
		return nil
	}
	var fd *ast.FuncDecl
	for _, d := range pf.file.Decls {
		if d, ok := d.(*ast.FuncDecl); ok && d.Name.Name == fn.Name() && pf.fset.Position(d.Name.Pos()).Offset == pos.Offset {
			fd = d
		}
	}
	if fd == nil || fd.Body == nil || fd.Type.Results == nil {
		return nil
	}

	// Rewrite the function as a function literal, which can be
	// type-checked on its own in the function's package.
	text := func(n ast.Node) string {
		return string(pf.src[pf.fset.Position(n.Pos()).Offset:pf.fset.Position(n.End()).Offset])
	}
	var params []string
	for _, fl := range []*ast.FieldList{fd.Recv, fd.Type.Params} {
		if fl == nil {
			continue
		}
		for _, field := range fl.List {
			names := []string{"_"}
			if len(field.Names) > 0 {
				names = names[:0]
				for _, n := range field.Names {
					names = append(names, n.Name)
				}
			}
			for _, n := range names {
				params = append(params, n+" "+text(field.Type))
			}
		}
	}
	src := "func(" + strings.Join(params, ", ") + ") " + text(fd.Type.Results) + " " + text(fd.Body)
	lfset := token.NewFileSet()
	x, err := parser.ParseExprFrom(lfset, "", src, parser.SkipObjectResolution)
	if err != nil {
		return nil
	}
	lit, ok := x.(*ast.FuncLit)
	if !ok {
		return nil
	}

	// Instantiate type parameters, which are all basic types (see callee).
	if fd.Type.TypeParams != nil {
		subst := make(map[string]string)
		i := 0
		for _, field := range fd.Type.TypeParams.List {
			for _, n := range field.Names {
				subst[n.Name] = targs[i].String()
				i++
			}
		}
		ast.Inspect(lit, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok {
				if s, ok := subst[id.Name]; ok {
					id.Name = s
				}
			}
			return true
		})
	}

	// The body must be definitions, then a return.
	stmts := lit.Body.List
	if len(stmts) == 0 {
		return nil
	}
	ret, ok := stmts[len(stmts)-1].(*ast.ReturnStmt)
	if !ok || len(ret.Results) != 1 {
		return nil
	}
	for _, s := range stmts[:len(stmts)-1] {
		as, ok := s.(*ast.AssignStmt)
		if !ok || as.Tok != token.DEFINE || len(as.Lhs) != 1 || len(as.Rhs) != 1 {
			return nil
		}
		if _, ok := as.Lhs[0].(*ast.Ident); !ok {
			return nil
		}
	}

	info := &types.Info{
		Types: make(map[ast.Expr]types.TypeAndValue),
		Defs:  make(map[*ast.Ident]types.Object),
		Uses:  make(map[*ast.Ident]types.Object),
	}
	// Identifiers resolve as if at fn's declaration, in its file's scope
	// (for imports). The literal's own positions, from lfset, are small,
	// so its parameters are in scope there.
	if err := types.CheckExpr(lfset, fn.Pkg(), fn.Pos(), lit, info); err != nil {
		return nil
	}
	inl := &inlined{info: info, ret: ret.Results[0]}
	for _, field := range lit.Type.Params.List {
		for _, n := range field.Names {
			inl.params = append(inl.params, info.Defs[n])
		}
	}
	for _, s := range stmts[:len(stmts)-1] {
		as := s.(*ast.AssignStmt)
		obj := info.Defs[as.Lhs[0].(*ast.Ident)]
		if obj == nil {
			return nil
		}
		inl.locals = append(inl.locals, local{obj, as.Rhs[0]})
	}
	return inl
}

func parseFile(name string) *parsedFile {
	if pf, ok := inlines.files[name]; ok {
		return pf
	}
	var pf *parsedFile
	if src, err := os.ReadFile(name); err == nil {
		fset := token.NewFileSet()
		if file, err := parser.ParseFile(fset, name, src, parser.SkipObjectResolution); err == nil {
			pf = &parsedFile{fset, src, file}
		}
	}
	inlines.files[name] = pf
	return pf
}

// callRange returns the range of a call's value, for builtins, math/bits
// functions, and inlinable helpers.
func (f *Facts) callRange(call *ast.CallExpr, en *env) (Interval, bool) {
	if id, ok := unparen(call.Fun).(*ast.Ident); ok {
		if b, ok := f.obj(id, en).(*types.Builtin); ok {
			return f.builtinRange(b.Name(), call, en)
		}
	}
	if fn, _, _, ok := f.callee(call, en); ok && fn.Pkg() != nil && fn.Pkg().Path() == "math/bits" && len(call.Args) == 1 {
		return f.bitsRange(fn.Name(), call.Args[0], en)
	}
	if body, ben, ok := f.inline(call, en); ok {
		return f.goRange(body, ben)
	}
	if fn, _, _, ok := f.callee(call, en); ok && fn.Pkg() != nil && strings.HasPrefix(fn.Pkg().Path(), "cmd/") {
		return constReturns(f.res.Fset, fn)
	}
	return Interval{}, false
}

func (f *Facts) builtinRange(name string, call *ast.CallExpr, en *env) (Interval, bool) {
	switch name {
	case "len", "cap":
		return Interval{Lo: zero}, true
	case "min", "max":
		var r Interval
		for i, a := range call.Args {
			ar, ok := f.goRange(a, en)
			if !ok {
				return Interval{}, false
			}
			if i == 0 {
				r = ar
				continue
			}
			if name == "min" {
				r = minIv(r, ar)
			} else {
				r = negIv(minIv(negIv(r), negIv(ar)))
			}
		}
		return r, len(call.Args) > 0
	}
	return Interval{}, false
}

// minIv returns the range of min(x, y) for x ∈ a, y ∈ b.
func minIv(a, b Interval) Interval {
	var r Interval
	if a.Lo != nil && b.Lo != nil {
		r.Lo = minBig(a.Lo, b.Lo)
	}
	switch {
	case a.Hi == nil:
		r.Hi = b.Hi
	case b.Hi == nil:
		r.Hi = a.Hi
	default:
		r.Hi = minBig(a.Hi, b.Hi)
	}
	return r
}

// bitsRange returns the range of math/bits function name applied to x.
// Their argument is unsigned. Those without a size suffix take a uint,
// which may have 32 or 64 bits.
func (f *Facts) bitsRange(name string, x ast.Expr, en *env) (Interval, bool) {
	var base string
	for _, b := range []string{"LeadingZeros", "TrailingZeros", "OnesCount", "Len"} {
		if strings.HasPrefix(name, b) {
			base = b
			break
		}
	}
	var n int64
	switch name[len(base):] {
	case "8":
		n = 8
	case "16":
		n = 16
	case "32":
		n = 32
	case "64":
		n = 64
	case "":
		n = 0
	default:
		return Interval{}, false
	}
	if base == "" {
		return Interval{}, false
	}
	xr, ok := f.goRange(x, en)
	if !ok || !xr.nonneg() {
		return Interval{}, false
	}
	bitlen := func(b *big.Int) int64 { return int64(b.BitLen()) }
	if n == 0 {
		// uint: bound the result by its width on either host.
		return Range(0, 64), true
	}
	all := Range(0, n)
	nz := xr.Lo.Sign() > 0 || f.excluded(x, en, zero)
	switch base {
	case "Len":
		if xr.Hi == nil {
			return Interval{Lo: big.NewInt(bitlen(xr.Lo)), Hi: big.NewInt(n)}, true
		}
		return Range(bitlen(xr.Lo), bitlen(xr.Hi)), true
	case "LeadingZeros":
		if xr.Hi == nil {
			return Range(0, n-bitlen(xr.Lo)), true
		}
		return Range(n-bitlen(xr.Hi), n-bitlen(xr.Lo)), true
	case "TrailingZeros":
		if nz {
			hi := n - 1
			if xr.Hi != nil {
				hi = min(hi, bitlen(xr.Hi)-1)
			}
			return Range(0, hi), true
		}
		return all, true
	case "OnesCount":
		r := all
		if nz {
			r.Lo = one
		}
		if xr.Hi != nil {
			r.Hi = big.NewInt(min(n, bitlen(xr.Hi)))
		}
		return r, true
	}
	return Interval{}, false
}
