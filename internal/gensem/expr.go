package gensem

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math"
)

// Env evaluates the Go expressions of one rule, as rulegen's generated
// code would, given the rule's variable bindings.
type Env struct {
	Info *types.Info
	U    *Universe
	Cfg  *Config
	V    *Value // the value being rewritten (v)
	Vars map[types.Object]GoVal
}

// Eval evaluates x.
func (e *Env) Eval(x ast.Expr) (GoVal, error) {
	if tv, ok := e.Info.Types[x]; ok && tv.Value != nil {
		if isOpType(tv.Type) {
			return e.opConst(x)
		}
		return fromConstant(tv.Value, tv.Type)
	}
	switch x := x.(type) {
	case *ast.ParenExpr:
		return e.Eval(x.X)
	case *ast.Ident:
		return e.ident(x)
	case *ast.SelectorExpr:
		return e.selector(x)
	case *ast.IndexExpr:
		return e.index(x)
	case *ast.UnaryExpr:
		return e.unary(x)
	case *ast.BinaryExpr:
		return e.binary(x)
	case *ast.CallExpr:
		return e.call(x)
	}
	return GoVal{}, unsupported("expression %s", types.ExprString(x))
}

// EvalBool evaluates a boolean expression.
func (e *Env) EvalBool(x ast.Expr) (bool, error) {
	g, err := e.Eval(x)
	if err != nil {
		return false, err
	}
	if basicInfo(g.T) != infoBool {
		return false, unsupported("non-bool condition %s", types.ExprString(x))
	}
	return g.I != 0, nil
}

func isOpType(t types.Type) bool {
	n, ok := t.(*types.Named)
	return ok && n.Obj().Name() == "Op" && n.Obj().Pkg() != nil
}

func (e *Env) opConst(x ast.Expr) (GoVal, error) {
	var id *ast.Ident
	switch x := x.(type) {
	case *ast.Ident:
		id = x
	case *ast.SelectorExpr:
		id = x.Sel
	case *ast.ParenExpr:
		return e.opConst(x.X)
	}
	if id != nil {
		if c, ok := e.Info.Uses[id].(*types.Const); ok && len(c.Name()) > 2 && c.Name()[:2] == "Op" {
			name := c.Name()[2:]
			if name == "Invalid" {
				name = ""
			}
			return GoVal{T: c.Type(), X: Op(name)}, nil
		}
	}
	return GoVal{}, unsupported("op expression %s", types.ExprString(x))
}

func (e *Env) ident(x *ast.Ident) (GoVal, error) {
	obj := e.Info.Uses[x]
	if obj == nil {
		obj = e.Info.Defs[x]
	}
	if g, ok := e.Vars[obj]; ok {
		return g, nil
	}
	if _, ok := obj.(*types.Nil); ok {
		return GoVal{}, nil
	}
	if v, ok := obj.(*types.Var); ok && v.Pkg() != nil && v.Parent() != v.Pkg().Scope() {
		switch x.Name {
		case "v":
			return GoVal{T: v.Type(), X: e.V}, nil
		case "config":
			return GoVal{T: v.Type(), X: e.Cfg}, nil
		case "typ":
			return GoVal{T: v.Type(), X: typStruct{}}, nil
		case "b":
			return GoVal{T: v.Type(), X: blockRef{}}, nil
		}
	}
	return GoVal{}, unsupported("identifier %s", x.Name)
}

func (e *Env) selector(x *ast.SelectorExpr) (GoVal, error) {
	t := e.Info.TypeOf(x)
	if isPkg(e.Info, x.X) {
		if v, ok := e.Info.Uses[x.Sel].(*types.Var); ok && v.Pkg() != nil && v.Pkg().Name() == "types" {
			switch name := v.Name(); name {
			case "Types":
				return GoVal{T: t, X: typesArray{}}, nil
			case "TypeFlags", "TypeMem", "TypeVoid":
				return GoVal{T: t, X: e.U.Named(name[4:])}, nil
			}
		}
		return GoVal{}, unsupported("selector %s", types.ExprString(x))
	}
	if _, ok := e.Info.Uses[x.Sel].(*types.Var); !ok {
		return GoVal{}, unsupported("method value %s", types.ExprString(x))
	}
	recv, err := e.Eval(x.X)
	if err != nil {
		return GoVal{}, err
	}
	return e.field(recv, x.Sel.Name, t)
}

// isPkg reports whether x names an imported package.
func isPkg(info *types.Info, x ast.Expr) bool {
	id, ok := x.(*ast.Ident)
	if !ok {
		return false
	}
	_, ok = info.Uses[id].(*types.PkgName)
	return ok
}

func (e *Env) field(recv GoVal, name string, t types.Type) (GoVal, error) {
	switch r := recv.X.(type) {
	case *Value:
		if r == nil {
			return GoVal{}, &Panic{"nil pointer dereference"}
		}
		switch name {
		case "Type":
			return GoVal{T: t, X: r.Type}, nil
		case "Op":
			return GoVal{T: t, X: Op(r.OpName())}, nil
		case "AuxInt":
			return mkInt(t, uint64(r.AuxInt)), nil
		case "Uses":
			return mkInt(t, uint64(r.Uses)), nil
		case "Args":
			return GoVal{T: t, X: r.Args}, nil
		case "Aux":
			if r.Aux != nil {
				return GoVal{T: t, X: r.Aux}, nil
			}
		case "Block":
			if r == e.V {
				return GoVal{T: t, X: blockRef{}}, nil
			}
		}
	case blockRef:
		if name == "Func" {
			return GoVal{T: t, X: funcRef{}}, nil
		}
	case funcRef:
		if name == "Pass" {
			return GoVal{T: t, X: passRef{}}, nil
		}
	case passRef:
		if name == "Name" && e.Cfg.Pass != "" {
			return GoVal{T: t, S: e.Cfg.Pass}, nil
		}
	case ctxtRef:
		if name == "Arch" {
			return GoVal{T: t, X: ctxtArchRef{}}, nil
		}
	case ctxtArchRef:
		if name == "Name" {
			return GoVal{T: t, S: e.Cfg.Arch}, nil
		}
	case *Config:
		switch name {
		case "PtrSize":
			return mkInt(t, uint64(r.PtrSize)), nil
		case "RegSize":
			return mkInt(t, uint64(r.RegSize)), nil
		case "BigEndian":
			return mkBool(t, r.BigEndian), nil
		case "Arch":
			return GoVal{T: t, S: r.Arch}, nil
		case "Ctxt":
			return GoVal{T: t, X: ctxtRef{}}, nil
		}
	case typStruct:
		if ty := e.U.Named(name); ty != nil {
			return GoVal{T: t, X: ty}, nil
		}
	case structFields:
		if f, ok := r[name]; ok {
			return f, nil
		}
		if f, ok := r[lowerFirst(name)]; ok {
			return f, nil
		}
	}
	return GoVal{}, unsupported("field %s of %v", name, recv.T)
}

func (e *Env) index(x *ast.IndexExpr) (GoVal, error) {
	recv, err := e.Eval(x.X)
	if err != nil {
		return GoVal{}, err
	}
	t := e.Info.TypeOf(x)
	switch r := recv.X.(type) {
	case []*Value:
		i, err := e.Eval(x.Index)
		if err != nil {
			return GoVal{}, err
		}
		if int64(i.I) < 0 || int64(i.I) >= int64(len(r)) {
			return GoVal{}, &Panic{fmt.Sprintf("index out of range [%d] with length %d", int64(i.I), len(r))}
		}
		return GoVal{T: t, X: r[i.I]}, nil
	case typesArray:
		var id *ast.Ident
		switch ix := x.Index.(type) {
		case *ast.Ident:
			id = ix
		case *ast.SelectorExpr:
			id = ix.Sel
		}
		if id != nil {
			if ty := e.U.ByKindName(id.Name); ty != nil {
				return GoVal{T: t, X: ty}, nil
			}
		}
	}
	return GoVal{}, unsupported("index expression %s", types.ExprString(x))
}

func (e *Env) unary(x *ast.UnaryExpr) (GoVal, error) {
	a, err := e.Eval(x.X)
	if err != nil {
		return GoVal{}, err
	}
	t := e.Info.TypeOf(x)
	switch info := basicInfo(t); {
	case x.Op == token.NOT && info == infoBool:
		return mkBool(t, a.I == 0), nil
	case x.Op == token.SUB && info == infoInt:
		return mkInt(t, -a.I), nil
	case x.Op == token.SUB && info == infoFloat:
		return mkFloat(t, -a.F), nil
	case x.Op == token.XOR && info == infoInt:
		return mkInt(t, ^a.I), nil
	case x.Op == token.ADD:
		return a, nil
	}
	return GoVal{}, unsupported("unary %s", types.ExprString(x))
}

func (e *Env) binary(x *ast.BinaryExpr) (GoVal, error) {
	t := defaultType(e.Info.TypeOf(x))
	if x.Op == token.LAND || x.Op == token.LOR {
		a, err := e.EvalBool(x.X)
		if err != nil {
			return GoVal{}, err
		}
		if a == (x.Op == token.LOR) {
			return mkBool(t, a), nil
		}
		b, err := e.EvalBool(x.Y)
		return mkBool(t, b), err
	}
	a, err := e.Eval(x.X)
	if err != nil {
		return GoVal{}, err
	}
	b, err := e.Eval(x.Y)
	if err != nil {
		return GoVal{}, err
	}
	switch x.Op {
	case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ:
		return e.compare(x, a, b, t)
	case token.SHL, token.SHR:
		return shift(x.Op, a, b, t)
	}
	switch basicInfo(t) {
	case infoInt:
		return intArith(x.Op, a, b, t)
	case infoFloat:
		var r float64
		switch x.Op {
		case token.ADD:
			r = a.F + b.F
		case token.SUB:
			r = a.F - b.F
		case token.MUL:
			r = a.F * b.F
		case token.QUO:
			r = a.F / b.F
		default:
			return GoVal{}, unsupported("float operator %s", x.Op)
		}
		if isFloat32(t) {
			// Each float32 operation rounds to float32.
			return mkFloat(t, float64(float32(r))), nil
		}
		return mkFloat(t, r), nil
	case infoString:
		if x.Op == token.ADD {
			return GoVal{T: t, S: a.S + b.S}, nil
		}
	}
	return GoVal{}, unsupported("binary %s", types.ExprString(x))
}

func intArith(op token.Token, a, b GoVal, t types.Type) (GoVal, error) {
	signed := !isUnsigned(t)
	var r uint64
	switch op {
	case token.ADD:
		r = a.I + b.I
	case token.SUB:
		r = a.I - b.I
	case token.MUL:
		r = a.I * b.I
	case token.AND:
		r = a.I & b.I
	case token.OR:
		r = a.I | b.I
	case token.XOR:
		r = a.I ^ b.I
	case token.AND_NOT:
		r = a.I &^ b.I
	case token.QUO, token.REM:
		if b.I == 0 {
			return GoVal{}, &Panic{"integer divide by zero"}
		}
		if signed {
			x, y := int64(a.I), int64(b.I)
			w := intBits(t)
			if y == -1 && x == sext(1<<uint(w-1), w) {
				// Go defines the most negative value / -1 to wrap.
				if op == token.QUO {
					r = uint64(x)
				} else {
					r = 0
				}
			} else if op == token.QUO {
				r = uint64(x / y)
			} else {
				r = uint64(x % y)
			}
		} else if op == token.QUO {
			r = a.I / b.I
		} else {
			r = a.I % b.I
		}
	default:
		return GoVal{}, unsupported("integer operator %s", op)
	}
	return mkInt(t, r), nil
}

func shift(op token.Token, a, b GoVal, t types.Type) (GoVal, error) {
	if basicInfo(t) != infoInt {
		return GoVal{}, unsupported("shift of %v", t)
	}
	if !isUnsigned(b.T) && int64(b.I) < 0 {
		return GoVal{}, &Panic{"negative shift amount"}
	}
	n := b.I
	w := uint64(intBits(t))
	if op == token.SHL {
		if n >= w {
			return mkInt(t, 0), nil
		}
		return mkInt(t, a.I<<n), nil
	}
	if isUnsigned(t) {
		if n >= w {
			return mkInt(t, 0), nil
		}
		return mkInt(t, a.I>>n), nil
	}
	n = min(n, 63)
	return mkInt(t, uint64(int64(a.I)>>n)), nil
}

func (e *Env) compare(x *ast.BinaryExpr, a, b GoVal, t types.Type) (GoVal, error) {
	var c int // -1, 0, 1; or eq only
	eqOnly := false
	ty := a.T
	if ty == nil || basicInfo(ty) == infoOther {
		ty = b.T
	}
	info := basicInfo(ty)
	if a.X != nil || b.X != nil {
		info = infoOther // ops, values, types
	}
	switch info {
	case infoInt:
		switch {
		case a.I == b.I:
			c = 0
		case isUnsigned(ty) && a.I < b.I, !isUnsigned(ty) && int64(a.I) < int64(b.I):
			c = -1
		default:
			c = 1
		}
	case infoFloat:
		if math.IsNaN(a.F) || math.IsNaN(b.F) {
			return mkBool(t, x.Op == token.NEQ), nil
		}
		switch {
		case a.F == b.F:
			c = 0
		case a.F < b.F:
			c = -1
		default:
			c = 1
		}
	case infoBool:
		eqOnly = true
		if a.I != b.I {
			c = 1
		}
	case infoString:
		switch {
		case a.S == b.S:
		case a.S < b.S:
			c = -1
		default:
			c = 1
		}
	default:
		eqOnly = true
		if !sameRef(a.X, b.X) {
			c = 1
		}
	}
	var r bool
	switch x.Op {
	case token.EQL:
		r = c == 0
	case token.NEQ:
		r = c != 0
	default:
		if eqOnly {
			return GoVal{}, unsupported("ordered comparison %s", types.ExprString(x))
		}
		switch x.Op {
		case token.LSS:
			r = c < 0
		case token.LEQ:
			r = c <= 0
		case token.GTR:
			r = c > 0
		case token.GEQ:
			r = c >= 0
		}
	}
	return mkBool(t, r), nil
}

// sameRef compares reference-like values: pointers by identity, ops by name.
func sameRef(a, b any) bool {
	if isNilRef(a) && isNilRef(b) {
		return true
	}
	switch a := a.(type) {
	case *Value:
		b, ok := b.(*Value)
		return ok && a == b
	case *Type:
		b, ok := b.(*Type)
		return ok && a == b
	case Op:
		b, ok := b.(Op)
		return ok && a == b
	case *Sym:
		b, ok := b.(*Sym)
		return ok && a == b
	}
	return false
}

func isNilRef(x any) bool {
	switch x := x.(type) {
	case nil:
		return true
	case *Value:
		return x == nil
	case *Type:
		return x == nil
	}
	return false
}

func (e *Env) call(x *ast.CallExpr) (GoVal, error) {
	t := e.Info.TypeOf(x)
	if tv := e.Info.Types[x.Fun]; tv.IsType() {
		if len(x.Args) != 1 {
			return GoVal{}, unsupported("conversion %s", types.ExprString(x))
		}
		a, err := e.Eval(x.Args[0])
		if err != nil {
			return GoVal{}, err
		}
		return convert(a, tv.Type)
	}
	fun := x.Fun
	if ix, ok := fun.(*ast.IndexExpr); ok { // explicit instantiation
		fun = ix.X
	}
	var id *ast.Ident
	var recv ast.Expr
	switch f := fun.(type) {
	case *ast.Ident:
		id = f
	case *ast.SelectorExpr:
		id = f.Sel
		if !isPkg(e.Info, f.X) {
			recv = f.X
		}
	case *ast.ParenExpr:
		return GoVal{}, unsupported("call %s", types.ExprString(x))
	}
	if id == nil {
		return GoVal{}, unsupported("call %s", types.ExprString(x))
	}
	obj := e.Info.Uses[id]
	args := make([]GoVal, len(x.Args))
	for i, a := range x.Args {
		g, err := e.Eval(a)
		if err != nil {
			return GoVal{}, err
		}
		args[i] = g
	}
	switch obj := obj.(type) {
	case *types.Builtin:
		return builtin(obj.Name(), args, t)
	case *types.Func:
		if recv != nil {
			r, err := e.Eval(recv)
			if err != nil {
				return GoVal{}, err
			}
			return e.method(r, obj.Name(), args, t)
		}
		h := helpers[helperKey(obj)]
		if h == nil {
			return GoVal{}, unsupported("function %s", obj.Name())
		}
		return callHelper(h, e, obj, args, t)
	}
	return GoVal{}, unsupported("call %s", types.ExprString(x))
}

// helperKey names a function: its package's name and its name with the
// first letter lowered, so that ssa.IsPowerOfTwo (in newer trees, where
// helpers are exported from package ssa) and isPowerOfTwo (in older trees)
// are both "isPowerOfTwo". Functions from math and math/bits keep their
// package qualifier.
func helperKey(f *types.Func) string {
	if p := f.Pkg(); p != nil && (p.Path() == "math" || p.Path() == "math/bits") {
		return p.Name() + "." + f.Name()
	}
	return lowerFirst(f.Name())
}

func builtin(name string, args []GoVal, t types.Type) (GoVal, error) {
	switch name {
	case "min", "max":
		if len(args) == 0 {
			break
		}
		r := args[0]
		for _, a := range args[1:] {
			var less bool
			switch basicInfo(t) {
			case infoInt:
				if isUnsigned(t) {
					less = a.I < r.I
				} else {
					less = int64(a.I) < int64(r.I)
				}
			case infoFloat:
				if math.IsNaN(a.F) || math.IsNaN(r.F) {
					return mkFloat(t, math.NaN()), nil
				}
				less = a.F < r.F || a.F == r.F && math.Signbit(a.F)
				if name == "max" {
					less = a.F < r.F || a.F == r.F && !math.Signbit(a.F)
				}
			default:
				return GoVal{}, unsupported("%s of %v", name, t)
			}
			if less == (name == "min") {
				r = a
			}
		}
		r.T = t
		return r, nil
	}
	return GoVal{}, unsupported("builtin %s", name)
}

// method calls a method of *types.Type.
func (e *Env) method(recv GoVal, name string, args []GoVal, t types.Type) (GoVal, error) {
	ty, ok := recv.X.(*Type)
	if !ok {
		return GoVal{}, unsupported("method %s on %v", name, recv.T)
	}
	if ty == nil {
		return GoVal{}, &Panic{"nil *types.Type"}
	}
	switch name {
	case "Size", "Alignment":
		if ty.Kind == TTuple || ty.Kind == TMem || ty.Kind == TFlags {
			return GoVal{}, unsupported("%s of %v", name, ty)
		}
		return mkInt(t, uint64(ty.Size)), nil
	case "IsSigned":
		return mkBool(t, ty.IsSigned()), nil
	case "IsUnsigned":
		return mkBool(t, ty.Kind == TUint), nil
	case "IsInteger":
		return mkBool(t, ty.IsInteger()), nil
	case "IsFloat":
		return mkBool(t, ty.IsFloat()), nil
	case "IsBoolean":
		return mkBool(t, ty.IsBoolean()), nil
	case "IsPtr", "IsPtrShaped", "IsUnsafePtr":
		return mkBool(t, ty.IsPtr()), nil
	case "IsUintptr":
		return mkBool(t, ty.IsUintptr()), nil
	case "IsTuple":
		return mkBool(t, ty.IsTuple()), nil
	case "IsFlags":
		return mkBool(t, ty.IsFlags()), nil
	case "IsMemory":
		return mkBool(t, ty.IsMemory()), nil
	case "Compare":
		// types.CMPeq is 0; other types compare as CMPlt or CMPgt.
		o, _ := args[0].X.(*Type)
		if o == ty {
			return mkInt(t, 0), nil
		}
		return mkInt(t, uint64(1)), nil
	case "IsComplex", "IsString", "IsSlice", "IsInterface", "IsStruct", "IsArray", "IsSIMD", "IsVoid", "IsResults", "IsChan", "IsMap", "IsFuncArgStruct":
		return mkBool(t, false), nil
	}
	return GoVal{}, unsupported("method %s", name)
}

// callHelper calls h, treating a panic in h itself (as from a helper whose
// signature differs in this revision) as unsupported.
func callHelper(h helper, e *Env, obj *types.Func, args []GoVal, t types.Type) (g GoVal, err error) {
	defer func() {
		if r := recover(); r != nil {
			err = unsupported("helper %s: %v", obj.Name(), r)
		}
	}()
	return h(e, args, t)
}
