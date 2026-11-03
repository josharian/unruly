package loweringcoverage

import (
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// tri is a three-valued truth value.
type tri uint8

const (
	maybe tri = iota
	no
	yes
)

func triOf(b bool) tri {
	if b {
		return yes
	}
	return no
}

func (t tri) val() val {
	switch t {
	case yes:
		return boolVal(true)
	case no:
		return boolVal(false)
	}
	return unknown
}

// A val is the abstract value of a Go expression in a rule.
type val struct {
	k    vkind
	b    bool
	i    int64
	t    *typ
	term *term
	op   string // an op constant, such as "SB" for OpSB
}

type vkind uint8

const (
	vUnknown vkind = iota
	vBool
	vInt
	vType
	vTerm
	vOp
	vConfig
	vNil
	vSym // a non-nil symbol
)

var unknown = val{}

func boolVal(b bool) val  { return val{k: vBool, b: b} }
func intVal(i int64) val  { return val{k: vInt, i: i} }
func typVal(t *typ) val   { return val{k: vType, t: t} }
func termVal(t *term) val { return val{k: vTerm, term: t} }

func (v val) tri() tri {
	if v.k != vBool {
		return maybe
	}
	return triOf(v.b)
}

// An env evaluates Go expressions of rule conditions and results with
// three-valued logic: anything it does not model is unknown, and unknown
// propagates (except through && and || short circuits).
type env struct {
	arch  *archInfo
	info  *types.Info // may be nil
	vars  map[string]val
	knobs map[string]int64 // buildcfg settings, such as "GOPPC64"
}

func (e *env) bind(name string, v val) { e.vars[name] = v }

func (e *env) eval(x ast.Expr) val {
	if e.info != nil {
		if tv, ok := e.info.Types[x]; ok && tv.Value != nil {
			switch tv.Value.Kind() {
			case constant.Bool:
				return boolVal(constant.BoolVal(tv.Value))
			case constant.Int:
				if i, ok := constant.Int64Val(tv.Value); ok {
					return intVal(i)
				}
			}
		}
	}
	switch x := x.(type) {
	case *ast.ParenExpr:
		return e.eval(x.X)
	case *ast.TypeAssertExpr: // t.(*types.Type) in older rules
		return e.eval(x.X)
	case *ast.BasicLit:
		if x.Kind == token.INT {
			if i, err := strconv.ParseInt(x.Value, 0, 64); err == nil {
				return intVal(i)
			}
			if u, err := strconv.ParseUint(x.Value, 0, 64); err == nil {
				return intVal(int64(u))
			}
		}
		return unknown
	case *ast.Ident:
		return e.ident(x.Name)
	case *ast.UnaryExpr:
		v := e.eval(x.X)
		switch {
		case x.Op == token.NOT && v.k == vBool:
			return boolVal(!v.b)
		case x.Op == token.SUB && v.k == vInt:
			return intVal(-v.i)
		case x.Op == token.XOR && v.k == vInt:
			return intVal(^v.i)
		case x.Op == token.ADD:
			return v
		}
		return unknown
	case *ast.BinaryExpr:
		return e.binary(x)
	case *ast.SelectorExpr:
		return e.selector(x)
	case *ast.IndexExpr:
		// types.Types[types.TUINT8]
		if sel, ok := x.X.(*ast.SelectorExpr); ok && isPkg(sel.X, "types") && sel.Sel.Name == "Types" {
			if k, ok := x.Index.(*ast.SelectorExpr); ok {
				return e.basicType(k.Sel.Name)
			}
		}
		return unknown
	case *ast.CallExpr:
		return e.call(x)
	}
	return unknown
}

func isPkg(x ast.Expr, name string) bool {
	id, ok := x.(*ast.Ident)
	return ok && id.Name == name
}

func (e *env) ident(name string) val {
	if v, ok := e.vars[name]; ok {
		return v
	}
	switch name {
	case "true":
		return boolVal(true)
	case "false":
		return boolVal(false)
	case "nil":
		return val{k: vNil}
	case "config":
		return val{k: vConfig}
	}
	if op, ok := strings.CutPrefix(name, "Op"); ok && op != "" {
		return val{k: vOp, op: op}
	}
	return unknown
}

func (e *env) basicType(kind string) val {
	n := typNames(e.arch.ptrSize)
	m := map[string]string{
		"TINT8": "Int8", "TINT16": "Int16", "TINT32": "Int32", "TINT64": "Int64",
		"TUINT8": "UInt8", "TUINT16": "UInt16", "TUINT32": "UInt32", "TUINT64": "UInt64",
		"TINT": "Int", "TUINT": "UInt", "TUINTPTR": "Uintptr", "TBOOL": "Bool",
		"TFLOAT32": "Float32", "TFLOAT64": "Float64",
	}
	if t := n[m[kind]]; t != nil {
		return typVal(t)
	}
	return unknown
}

func (e *env) selector(x *ast.SelectorExpr) val {
	name := x.Sel.Name
	switch {
	case isPkg(x.X, "typ"):
		if t := typNames(e.arch.ptrSize)[name]; t != nil {
			return typVal(t)
		}
		return unknown
	case isPkg(x.X, "types"):
		switch name {
		case "TypeMem":
			return typVal(&typ{name: "mem", kind: tMem, size: 0, align: 0, ptrs: no})
		case "TypeFlags":
			return typVal(&typ{name: "flags", kind: tFlags, size: 0, align: 0, ptrs: no})
		}
		return unknown
	case isPkg(x.X, "buildcfg"):
		if v, ok := e.knobs[name]; ok {
			return intVal(v)
		}
		return unknown
	case isPkg(x.X, "ssa"), isPkg(x.X, "ssaop"):
		return e.ident(name)
	}
	recv := e.eval(x.X)
	switch recv.k {
	case vConfig:
		switch name {
		case "PtrSize", "RegSize":
			return intVal(e.arch.ptrSize)
		}
	case vTerm:
		t := recv.term
		switch name {
		case "Type":
			if t.typ != nil {
				return typVal(t.typ)
			}
		case "Op":
			if t.op != nil {
				return val{k: vOp, op: t.op.QualifiedName()}
			}
		case "AuxInt":
			return t.auxint
		}
	}
	return unknown
}

// helperName normalizes a helper function name across revisions:
// ssa.Is32Bit and is32Bit are the same helper.
func helperName(fun ast.Expr) string {
	var name string
	switch f := fun.(type) {
	case *ast.Ident:
		name = f.Name
	case *ast.SelectorExpr:
		if !isPkg(f.X, "ssa") {
			return ""
		}
		name = f.Sel.Name
	default:
		return ""
	}
	r, n := utf8.DecodeRuneInString(name)
	return string(unicode.ToLower(r)) + name[n:]
}

func (e *env) call(x *ast.CallExpr) val {
	// Methods of types: t.Size(), t.Elem().HasPointers(), ...
	if sel, ok := x.Fun.(*ast.SelectorExpr); ok && len(x.Args) == 0 && !isPkg(sel.X, "ssa") {
		if recv := e.eval(sel.X); recv.k == vType {
			return recv.t.method(sel.Sel.Name)
		}
		return unknown
	}
	args := make([]val, len(x.Args))
	for i, a := range x.Args {
		args[i] = e.eval(a)
	}
	arg := func(i int) val {
		if i < len(args) {
			return args[i]
		}
		return unknown
	}
	tpred := func(f func(*typ) val) val {
		if a := arg(0); a.k == vType {
			return f(a.t)
		}
		return unknown
	}
	// Type predicates from ssa/rewrite.go, e.g.
	// func Is64BitInt(t *types.Type) bool { return t.Size() == 8 && t.IsInteger() }.
	sized := func(size int64, m string) val {
		return tpred(func(t *typ) val {
			return and(eqInt(t.method("Size"), size), t.method(m))
		})
	}
	ival := func(f func(int64) bool) val {
		if a := arg(0); a.k == vInt {
			return boolVal(f(a.i))
		}
		return unknown
	}
	conv := func(f func(int64) int64) val {
		if a := arg(0); a.k == vInt {
			return intVal(f(a.i))
		}
		return unknown
	}
	switch helperName(x.Fun) {
	case "is8BitInt":
		return sized(1, "IsInteger")
	case "is16BitInt":
		return sized(2, "IsInteger")
	case "is32BitInt":
		return sized(4, "IsInteger")
	case "is64BitInt":
		return sized(8, "IsInteger")
	case "is32BitFloat":
		return sized(4, "IsFloat")
	case "is64BitFloat":
		return sized(8, "IsFloat")
	case "isPtr":
		return tpred(func(t *typ) val { return t.method("IsPtrShaped") })
	case "isSigned":
		return tpred(func(t *typ) val { return t.method("IsSigned") })
	case "is32Bit":
		return ival(func(n int64) bool { return n == int64(int32(n)) })
	case "isU32Bit":
		return ival(func(n int64) bool { return n == int64(uint32(n)) })
	case "is16Bit":
		return ival(func(n int64) bool { return n == int64(int16(n)) })
	case "isU16Bit":
		return ival(func(n int64) bool { return n == int64(uint16(n)) })
	case "is20Bit":
		return ival(func(n int64) bool { return -(1<<19) <= n && n < (1<<19) })
	case "isU12Bit":
		return ival(func(n int64) bool { return 0 <= n && n < (1<<12) })
	case "isU8Bit":
		return ival(func(n int64) bool { return n == int64(uint8(n)) })
	case "is8Bit":
		return ival(func(n int64) bool { return n == int64(int8(n)) })
	case "logLargeCopy", "logLargeCopyValue":
		// Logs and returns true (ssa/rewrite.go).
		return boolVal(true)
	case "moveSize":
		// ssa/rewrite.go:
		//	case align%8 == 0 && c.PtrSize == 8: return 8
		//	case align%4 == 0: return 4
		//	case align%2 == 0: return 2
		//	default: return 1
		a := arg(0)
		if a.k != vInt {
			return unknown
		}
		switch {
		case a.i%8 == 0 && e.arch.ptrSize == 8:
			return intVal(8)
		case a.i%4 == 0:
			return intVal(4)
		case a.i%2 == 0:
			return intVal(2)
		}
		return intVal(1)
	case "makeValAndOff":
		// ssa/rewrite.go (and older ssa/op.go): val in the high 32 bits,
		// off in the low 32 bits.
		v, o := arg(0), arg(1)
		if v.k != vInt || o.k != vInt {
			return unknown
		}
		return intVal(int64(int32(v.i))<<32 | int64(uint32(o.i)))
	case "int64", "int":
		return conv(func(n int64) int64 { return n })
	case "int32":
		return conv(func(n int64) int64 { return int64(int32(n)) })
	case "int16":
		return conv(func(n int64) int64 { return int64(int16(n)) })
	case "int8":
		return conv(func(n int64) int64 { return int64(int8(n)) })
	case "uint32":
		return conv(func(n int64) int64 { return int64(uint32(n)) })
	case "uint16":
		return conv(func(n int64) int64 { return int64(uint16(n)) })
	case "uint8":
		return conv(func(n int64) int64 { return int64(uint8(n)) })
	}
	return unknown
}

func eqInt(v val, n int64) val {
	if v.k != vInt {
		return unknown
	}
	return boolVal(v.i == n)
}

func and(a, b val) val {
	if a.k == vBool && !a.b || b.k == vBool && !b.b {
		return boolVal(false)
	}
	if a.k == vBool && b.k == vBool {
		return boolVal(true)
	}
	return unknown
}

func or(a, b val) val {
	if a.k == vBool && a.b || b.k == vBool && b.b {
		return boolVal(true)
	}
	if a.k == vBool && b.k == vBool {
		return boolVal(false)
	}
	return unknown
}

func (e *env) binary(x *ast.BinaryExpr) val {
	switch x.Op {
	case token.LAND:
		return and(e.eval(x.X), e.eval(x.Y))
	case token.LOR:
		return or(e.eval(x.X), e.eval(x.Y))
	}
	a, b := e.eval(x.X), e.eval(x.Y)
	if x.Op == token.EQL || x.Op == token.NEQ {
		eq := equal(a, b)
		if x.Op == token.NEQ && eq.k == vBool {
			eq.b = !eq.b
		}
		return eq
	}
	if a.k != vInt || b.k != vInt {
		return unknown
	}
	i, j := a.i, b.i
	switch x.Op {
	case token.LSS:
		return boolVal(i < j)
	case token.LEQ:
		return boolVal(i <= j)
	case token.GTR:
		return boolVal(i > j)
	case token.GEQ:
		return boolVal(i >= j)
	case token.ADD:
		return intVal(i + j)
	case token.SUB:
		return intVal(i - j)
	case token.MUL:
		return intVal(i * j)
	case token.QUO:
		if j == 0 {
			return unknown
		}
		return intVal(i / j)
	case token.REM:
		if j == 0 {
			return unknown
		}
		return intVal(i % j)
	case token.AND:
		return intVal(i & j)
	case token.OR:
		return intVal(i | j)
	case token.XOR:
		return intVal(i ^ j)
	case token.AND_NOT:
		return intVal(i &^ j)
	case token.SHL:
		if j < 0 || j >= 64 {
			return unknown
		}
		return intVal(i << j)
	case token.SHR:
		if j < 0 || j >= 64 {
			return unknown
		}
		return intVal(i >> j)
	}
	return unknown
}

func equal(a, b val) val {
	if a.k == vSym && b.k == vNil || a.k == vNil && b.k == vSym {
		return boolVal(false)
	}
	if a.k != b.k || a.k == vUnknown {
		return unknown
	}
	switch a.k {
	case vBool:
		return boolVal(a.b == b.b)
	case vInt:
		return boolVal(a.i == b.i)
	case vOp:
		return boolVal(a.op == b.op)
	case vType:
		if a.t == b.t {
			return boolVal(true)
		}
		if a.t.name == b.t.name && a.t.kind != tUnknown {
			return boolVal(true)
		}
	case vNil:
		return boolVal(true)
	case vTerm:
		if a.term == b.term {
			return boolVal(true)
		}
	}
	return unknown
}
