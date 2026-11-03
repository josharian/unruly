package extelim

import (
	"go/ast"
	"go/constant"
	"go/token"
	"strings"
	"unicode"
	"unicode/utf8"
)

// This file is a small three-valued evaluator for the Go expressions in rule
// conditions and auxints. It knows integer arithmetic and conversions, a few
// pure helpers from rewrite.go, and the *types.Type predicates rules use to
// talk about a value's type. Everything else evaluates to unknown, so a
// condition that cannot be decided counts as possibly true.

// kind is the Go type of an evaluated value.
type kind uint8

const (
	kUnknown kind = iota
	kUntyped      // an untyped integer constant
	kInt8
	kInt16
	kInt32
	kInt64
	kUint8
	kUint16
	kUint32
	kUint64
	kBitField // ssa.arm64BitField: width | lsb<<8, an int16
	kBool
	kType // a *types.Type, abstracted as an ssaType
)

func (k kind) isInt() bool { return k >= kUntyped && k <= kBitField }

func (k kind) signed() bool {
	switch k {
	case kUint8, kUint16, kUint32, kUint64:
		return false
	}
	return true
}

func (k kind) bits() uint {
	switch k {
	case kInt8, kUint8:
		return 8
	case kInt16, kUint16, kBitField:
		return 16
	case kInt32, kUint32:
		return 32
	}
	return 64
}

// wrap truncates x to k's width and extends it back to 64 bits as k would.
func (k kind) wrap(x int64) int64 {
	n := k.bits()
	if n == 64 || k == kUntyped {
		return x
	}
	if k.signed() {
		return x << (64 - n) >> (64 - n)
	}
	return int64(uint64(x) << (64 - n) >> (64 - n))
}

var kindNames = map[string]kind{
	"int8": kInt8, "int16": kInt16, "int32": kInt32, "int64": kInt64, "int": kInt64,
	"uint8": kUint8, "byte": kUint8, "uint16": kUint16, "uint32": kUint32, "uint64": kUint64, "uint": kUint64, "uintptr": kUint64,
	"arm64BitField": kBitField, "Arm64BitField": kBitField,
}

// val is the result of evaluating an expression.
type val struct {
	k kind
	i int64 // an integer, wrapped to k
	b bool
	t ssaType
}

var unknown = val{}

func intVal(k kind, x int64) val { return val{k: k, i: k.wrap(x)} }
func boolVal(b bool) val         { return val{k: kBool, b: b} }

// env binds the names an expression may mention. A value variable's type is
// bound as "x.Type", and the rewritten value's type as "v.Type".
type env map[string]val

// eval evaluates e in env.
func eval(e ast.Expr, en env) val {
	switch e := e.(type) {
	case *ast.ParenExpr:
		return eval(e.X, en)
	case *ast.BasicLit:
		if e.Kind != token.INT {
			return unknown
		}
		c := constant.MakeFromLiteral(e.Value, e.Kind, 0)
		if x, ok := constant.Int64Val(c); ok {
			return val{k: kUntyped, i: x}
		}
		if x, ok := constant.Uint64Val(c); ok {
			return val{k: kUntyped, i: int64(x)}
		}
		return unknown
	case *ast.Ident:
		switch e.Name {
		case "true":
			return boolVal(true)
		case "false":
			return boolVal(false)
		}
		return en[e.Name]
	case *ast.SelectorExpr:
		if id, ok := e.X.(*ast.Ident); ok {
			if t, ok := typNames[id.Name+"."+e.Sel.Name]; ok {
				return val{k: kType, t: t}
			}
			return en[id.Name+"."+e.Sel.Name]
		}
		return unknown
	case *ast.UnaryExpr:
		x := eval(e.X, en)
		switch e.Op {
		case token.NOT:
			if x.k == kBool {
				return boolVal(!x.b)
			}
		case token.SUB:
			if x.k.isInt() {
				return intVal(x.k, -x.i)
			}
		case token.XOR:
			if x.k.isInt() {
				return intVal(x.k, ^x.i)
			}
		case token.ADD:
			return x
		}
		return unknown
	case *ast.BinaryExpr:
		return evalBinary(e, en)
	case *ast.CallExpr:
		return evalCall(e, en)
	}
	return unknown
}

func evalBinary(e *ast.BinaryExpr, en env) val {
	// && and || are three-valued: false && unknown is false.
	switch e.Op {
	case token.LAND, token.LOR:
		x, y := eval(e.X, en), eval(e.Y, en)
		short := e.Op == token.LOR // the value that decides the result
		if (x.k == kBool && x.b == short) || (y.k == kBool && y.b == short) {
			return boolVal(short)
		}
		if x.k == kBool && y.k == kBool {
			return boolVal(!short)
		}
		return unknown
	}
	x, y := eval(e.X, en), eval(e.Y, en)
	if x.k == kBool && y.k == kBool {
		switch e.Op {
		case token.EQL:
			return boolVal(x.b == y.b)
		case token.NEQ:
			return boolVal(x.b != y.b)
		}
		return unknown
	}
	if !x.k.isInt() || !y.k.isInt() {
		return unknown
	}
	if e.Op == token.SHL || e.Op == token.SHR {
		if !y.k.signed() || y.i >= 0 {
			s := uint64(y.i)
			if s >= 64 {
				s = 64
			}
			k := x.k
			switch {
			case e.Op == token.SHL && s >= 64:
				return intVal(k, 0)
			case e.Op == token.SHL:
				return intVal(k, x.i<<s)
			case k.signed() && s >= 64:
				return intVal(k, x.i>>63)
			case k.signed():
				return intVal(k, x.i>>s)
			case s >= 64:
				return intVal(k, 0)
			default:
				return intVal(k, int64(uint64(x.i)>>s))
			}
		}
		return unknown
	}
	k := x.k
	if k == kUntyped {
		k = y.k
	}
	a, b := x.i, y.i
	switch e.Op {
	case token.ADD:
		return intVal(k, a+b)
	case token.SUB:
		return intVal(k, a-b)
	case token.MUL:
		return intVal(k, a*b)
	case token.QUO, token.REM:
		if b == 0 {
			return unknown
		}
		var r int64
		switch {
		case k.signed() && e.Op == token.QUO:
			if a == -1<<63 && b == -1 {
				return unknown
			}
			r = a / b
		case k.signed():
			if b == -1 {
				r = 0
			} else {
				r = a % b
			}
		case e.Op == token.QUO:
			r = int64(uint64(a) / uint64(b))
		default:
			r = int64(uint64(a) % uint64(b))
		}
		return intVal(k, r)
	case token.AND:
		return intVal(k, a&b)
	case token.OR:
		return intVal(k, a|b)
	case token.XOR:
		return intVal(k, a^b)
	case token.AND_NOT:
		return intVal(k, a&^b)
	case token.EQL:
		return boolVal(a == b)
	case token.NEQ:
		return boolVal(a != b)
	}
	var less, eq bool
	if k.signed() {
		less, eq = a < b, a == b
	} else {
		less, eq = uint64(a) < uint64(b), a == b
	}
	switch e.Op {
	case token.LSS:
		return boolVal(less)
	case token.LEQ:
		return boolVal(less || eq)
	case token.GTR:
		return boolVal(!less && !eq)
	case token.GEQ:
		return boolVal(!less)
	}
	return unknown
}

// funcName returns the name of a called function or method, without an
// ssa. qualifier and with a lower-case first letter (rewrite.go's helpers
// have been exported and unexported over the years).
func funcName(fun ast.Expr) (recv ast.Expr, name string) {
	switch f := fun.(type) {
	case *ast.Ident:
		return nil, lower(f.Name)
	case *ast.SelectorExpr:
		if id, ok := f.X.(*ast.Ident); ok && id.Name == "ssa" {
			return nil, lower(f.Sel.Name)
		}
		return f.X, f.Sel.Name
	}
	return nil, ""
}

func lower(s string) string {
	r, n := utf8.DecodeRuneInString(s)
	return string(unicode.ToLower(r)) + s[n:]
}

func evalCall(e *ast.CallExpr, en env) val {
	recv, name := funcName(e.Fun)
	if recv != nil {
		// A method call: t.Size(), x.Type.IsSigned(), bfc.Width(), ...
		if len(e.Args) != 0 {
			return unknown
		}
		r := eval(recv, en)
		switch r.k {
		case kType:
			return r.t.method(name)
		case kBitField:
			switch name {
			case "Width", "width", "getARM64BFwidth":
				return intVal(kInt64, r.i&0xff)
			case "Lsb", "LSB", "lsb", "getARM64BFlsb":
				return intVal(kInt64, int64(uint64(r.i)>>8))
			}
		}
		return unknown
	}
	if name == "armBFAuxInt" && len(e.Args) == 2 {
		// armBFAuxInt(lsb, width) encodes an arm64BitField.
		lsb, w := eval(e.Args[0], en), eval(e.Args[1], en)
		if lsb.k.isInt() && w.k.isInt() && lsb.i >= 0 && lsb.i < 64 && w.i >= 1 && lsb.i+w.i <= 64 {
			return intVal(kBitField, w.i|lsb.i<<8)
		}
		return unknown
	}
	if len(e.Args) != 1 {
		return unknown
	}
	if k, ok := kindNames[name]; ok && k != kBitField {
		x := eval(e.Args[0], en)
		if !x.k.isInt() {
			return unknown
		}
		return intVal(k, x.i)
	}
	x := eval(e.Args[0], en)
	if x.k == kType {
		t := x.t
		switch name {
		case "is8BitInt":
			return boolVal(t.isInt() && t.size() == 1)
		case "is16BitInt":
			return boolVal(t.isInt() && t.size() == 2)
		case "is32BitInt":
			return boolVal(t.isInt() && t.size() == 4)
		case "is64BitInt":
			return boolVal(t.isInt() && t.size() == 8)
		case "isSigned":
			return boolVal(t.signed())
		}
		return unknown
	}
	if !x.k.isInt() {
		return unknown
	}
	c := x.i
	if !x.k.signed() && c < 0 {
		// A huge unsigned value: none of the helpers below take one.
		return unknown
	}
	switch name {
	case "is8Bit":
		return boolVal(c == int64(int8(c)))
	case "isU8Bit":
		return boolVal(c == int64(uint8(c)))
	case "is16Bit":
		return boolVal(c == int64(int16(c)))
	case "isU16Bit":
		return boolVal(c == int64(uint16(c)))
	case "is32Bit":
		return boolVal(c == int64(int32(c)))
	case "isU32Bit":
		return boolVal(c == int64(uint32(c)))
	case "is12Bit":
		return boolVal(-1<<11 <= c && c < 1<<11)
	case "isU12Bit":
		return boolVal(0 <= c && c < 1<<12)
	case "isPowerOfTwo":
		return boolVal(c > 0 && c&(c-1) == 0)
	}
	if x.k == kBool {
		switch name {
		case "b2i", "b2i32":
			if x.b {
				return intVal(kInt64, 1)
			}
			return intVal(kInt64, 0)
		}
	}
	return unknown
}

// mentions reports whether e mentions the selector or identifier name
// (such as "v.Type" or "c").
func mentions(e ast.Expr, name string) bool {
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.SelectorExpr:
			if id, ok := n.X.(*ast.Ident); ok && id.Name+"."+n.Sel.Name == name {
				found = true
			}
		case *ast.Ident:
			if n.Name == name {
				found = true
			}
		}
		return !found
	})
	return found
}

// callsWith reports whether e calls a function other than a known pure
// predicate with an argument that mentions name. A condition such as
// ZeroUpper32Bits(x) or isSignExtended(x) establishes facts about x that
// this package does not model.
func callsWith(e ast.Expr, name string) bool {
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return !found
		}
		recv, fn := funcName(call.Fun)
		if recv != nil || kindNames[fn] != 0 || strings.HasPrefix(fn, "is") && strings.HasSuffix(fn, "BitInt") || fn == "isSigned" {
			return true
		}
		for _, a := range call.Args {
			if mentions(a, name) {
				found = true
			}
		}
		return !found
	})
	return found
}
