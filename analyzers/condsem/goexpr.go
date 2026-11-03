package condsem

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"math/bits"
	"strings"
	"unicode"
	"unicode/utf8"
)

// gkind is the kind of a Go value in a condition or aux expression.
type gkind uint8

const (
	gTop   gkind = iota // unknown and immaterial (x.Uses, t.Size(), config...)
	gInt                // i holds the value, sign- or zero-extended per t
	gBool               // b
	gFloat              // f
	gOp                 // s: an op name, such as "LessThanU"
	gSym                // s: an opaque aux value, such as a symbol
	gValue              // v: an SSA value
	gNil
)

// gv is a Go value.
type gv struct {
	k gkind
	i uint64
	b bool
	f float64
	s string
	v val
	t types.Type
}

func (g gv) String() string {
	switch g.k {
	case gInt:
		if n, ok := g.t.(*types.Named); ok && strings.EqualFold(n.Obj().Name(), "FlagConstant") {
			return flagConstant(g.i).String()
		}
		if isSigned(g.t) {
			return fmt.Sprint(int64(g.i))
		}
		if g.i < 1<<20 {
			return fmt.Sprint(g.i)
		}
		return fmt.Sprintf("%#x", g.i)
	case gBool:
		return fmt.Sprint(g.b)
	case gFloat:
		return fmt.Sprint(g.f)
	case gOp, gSym:
		return g.s
	case gValue:
		return g.v.String()
	case gNil:
		return "nil"
	}
	return "?"
}

func basic(t types.Type) *types.Basic {
	if t == nil {
		return nil
	}
	b, _ := t.Underlying().(*types.Basic)
	return b
}

func isSigned(t types.Type) bool {
	b := basic(t)
	return b == nil || b.Info()&types.IsUnsigned == 0
}

// width returns the size of integer type t in bits.
func width(t types.Type) uint8 {
	b := basic(t)
	if b == nil {
		return 64
	}
	switch b.Kind() {
	case types.Int8, types.Uint8:
		return 8
	case types.Int16, types.Uint16:
		return 16
	case types.Int32, types.Uint32:
		return 32
	}
	return 64
}

// mkInt returns x converted to integer type t.
func mkInt(x uint64, t types.Type) gv {
	w := width(t)
	if isSigned(t) {
		x = uint64(sext(x, w))
	} else {
		x = trunc(x, w)
	}
	return gv{k: gInt, i: x, t: t}
}

func boolGV(b bool) gv { return gv{k: gBool, b: b, t: types.Typ[types.Bool]} }

var top = gv{k: gTop}

// goExpr evaluates a Go expression from a rule (a condition or the
// contents of [] or {}) in the rule's typed context.
func (c *ctx) goExpr(e ast.Expr) gv {
	if e == nil {
		unmodeled("missing expression")
	}
	tv := c.info.Types[e]
	if g, ok := c.opConst(e); ok {
		return g
	}
	if tv.Value != nil {
		return constGV(tv.Value, tv.Type)
	}
	switch e := e.(type) {
	case *ast.ParenExpr:
		return c.goExpr(e.X)
	case *ast.Ident:
		return c.ident(e)
	case *ast.SelectorExpr:
		if c.isPkg(e.X) {
			// A package-level variable, such as buildcfg.GOAMD64.
			return top
		}
		x := c.goExpr(e.X)
		if x.k == gTop || x.k == gValue {
			// Fields of values (x.Uses, x.Block, x.Type...) don't
			// affect what the value computes.
			return top
		}
		unmodeled("selector %s", types.ExprString(e))
	case *ast.UnaryExpr:
		x := c.goExpr(e.X)
		if x.k == gTop {
			return top
		}
		switch e.Op {
		case token.NOT:
			return boolGV(!x.b)
		case token.SUB:
			if x.k == gFloat {
				return gv{k: gFloat, f: -x.f, t: x.t}
			}
			return mkInt(-x.i, tv.Type)
		case token.XOR:
			return mkInt(^x.i, tv.Type)
		}
	case *ast.BinaryExpr:
		return c.binary(e, tv.Type)
	case *ast.CallExpr:
		return c.call(e, tv.Type)
	}
	unmodeled("expression %s", types.ExprString(e))
	return top
}

// isPkg reports whether e names an imported package.
func (c *ctx) isPkg(e ast.Expr) bool {
	id, ok := e.(*ast.Ident)
	if !ok {
		return false
	}
	_, ok = c.info.Uses[id].(*types.PkgName)
	return ok
}

func (c *ctx) ident(e *ast.Ident) gv {
	switch e.Name {
	case "nil":
		return gv{k: gNil}
	case "true", "false":
		return boolGV(e.Name == "true")
	}
	if g, ok := c.genv[e.Name]; ok {
		return g
	}
	if v, ok := c.env[e.Name]; ok {
		return gv{k: gValue, v: v}
	}
	if tvar := c.tr.Vars[e.Name]; tvar != nil {
		// A match variable not (yet) bound to a value, such as a type.
		return top
	}
	switch e.Name {
	case "v", "b", "config", "typ", "fe":
		return top
	}
	unmodeled("identifier %s", e.Name)
	return top
}

// opConst reports whether e is an Op constant (ssaop.OpARM64LessThanU),
// and if so returns its name without the Op and arch prefixes.
func (c *ctx) opConst(e ast.Expr) (gv, bool) {
	var id *ast.Ident
	switch e := e.(type) {
	case *ast.Ident:
		id = e
	case *ast.SelectorExpr:
		id = e.Sel
	default:
		return gv{}, false
	}
	obj, ok := c.info.Uses[id].(*types.Const)
	if !ok {
		return gv{}, false
	}
	n, ok := obj.Type().(*types.Named)
	if !ok || n.Obj().Name() != "Op" {
		return gv{}, false
	}
	name := strings.TrimPrefix(obj.Name(), "Op")
	name = strings.TrimPrefix(name, c.a.name)
	return gv{k: gOp, s: name, t: n}, true
}

func constGV(v constant.Value, t types.Type) gv {
	switch v.Kind() {
	case constant.Bool:
		return gv{k: gBool, b: constant.BoolVal(v), t: t}
	case constant.Int:
		if i, ok := constant.Int64Val(v); ok {
			return mkInt(uint64(i), t)
		}
		if u, ok := constant.Uint64Val(v); ok {
			return mkInt(u, t)
		}
	case constant.Float:
		f, _ := constant.Float64Val(v)
		return gv{k: gFloat, f: f, t: t}
	}
	unmodeled("constant %v", v)
	return top
}

func (c *ctx) binary(e *ast.BinaryExpr, t types.Type) gv {
	switch e.Op {
	case token.LAND:
		x := c.goExpr(e.X)
		if x.k == gBool && !x.b {
			return x
		}
		y := c.goExpr(e.Y)
		if y.k == gBool && !y.b {
			return y
		}
		if x.k == gTop || y.k == gTop {
			return top
		}
		return boolGV(true)
	case token.LOR:
		x := c.goExpr(e.X)
		if x.k == gBool && x.b {
			return x
		}
		y := c.goExpr(e.Y)
		if y.k == gBool && y.b {
			return y
		}
		if x.k == gTop || y.k == gTop {
			return top
		}
		return boolGV(false)
	}
	x, y := c.goExpr(e.X), c.goExpr(e.Y)
	if x.k == gTop || y.k == gTop {
		return top
	}
	switch e.Op {
	case token.EQL, token.NEQ:
		eq := c.goEqual(x, y)
		return boolGV(eq == (e.Op == token.EQL))
	case token.LSS, token.LEQ, token.GTR, token.GEQ:
		var cmp int
		switch {
		case x.k == gFloat && y.k == gFloat:
			if x.f != x.f || y.f != y.f {
				return boolGV(false)
			}
			cmp = compareFloat(x.f, y.f)
		case x.k == gInt && y.k == gInt:
			if isSigned(x.t) {
				cmp = compareInt(int64(x.i), int64(y.i))
			} else {
				cmp = compareUint(x.i, y.i)
			}
		default:
			unmodeled("comparison %s", types.ExprString(e))
		}
		switch e.Op {
		case token.LSS:
			return boolGV(cmp < 0)
		case token.LEQ:
			return boolGV(cmp <= 0)
		case token.GTR:
			return boolGV(cmp > 0)
		default:
			return boolGV(cmp >= 0)
		}
	}
	if x.k == gFloat && y.k == gFloat {
		var f float64
		switch e.Op {
		case token.ADD:
			f = x.f + y.f
		case token.SUB:
			f = x.f - y.f
		case token.MUL:
			f = x.f * y.f
		case token.QUO:
			f = x.f / y.f
		default:
			unmodeled("float op %s", e.Op)
		}
		if width(t) == 32 || (basic(t) != nil && basic(t).Kind() == types.Float32) {
			f = float64(float32(f))
		}
		return gv{k: gFloat, f: f, t: t}
	}
	if x.k != gInt || y.k != gInt {
		unmodeled("operands of %s", types.ExprString(e))
	}
	signed := isSigned(t)
	var r uint64
	switch e.Op {
	case token.ADD:
		r = x.i + y.i
	case token.SUB:
		r = x.i - y.i
	case token.MUL:
		r = x.i * y.i
	case token.QUO, token.REM:
		if y.i == 0 {
			impossible() // the generated code would panic
		}
		if signed {
			a, b := int64(x.i), int64(y.i)
			if b == -1 {
				if e.Op == token.QUO {
					r = uint64(-a)
				} else {
					r = 0
				}
			} else if e.Op == token.QUO {
				r = uint64(a / b)
			} else {
				r = uint64(a % b)
			}
		} else if e.Op == token.QUO {
			r = x.i / y.i
		} else {
			r = x.i % y.i
		}
	case token.AND:
		r = x.i & y.i
	case token.OR:
		r = x.i | y.i
	case token.XOR:
		r = x.i ^ y.i
	case token.AND_NOT:
		r = x.i &^ y.i
	case token.SHL, token.SHR:
		if isSigned(y.t) && int64(y.i) < 0 {
			impossible() // negative shift count panics
		}
		s := y.i
		if e.Op == token.SHL {
			if s >= 64 {
				r = 0
			} else {
				r = x.i << s
			}
		} else if signed {
			if s >= 64 {
				s = 63
			}
			r = uint64(int64(x.i) >> s)
		} else {
			if s >= 64 {
				r = 0
			} else {
				r = x.i >> s
			}
		}
	default:
		unmodeled("operator %s", e.Op)
	}
	return mkInt(r, t)
}

func (c *ctx) goEqual(x, y gv) bool {
	switch {
	case x.k == gNil || y.k == gNil:
		return x.k == y.k
	case x.k != y.k:
		unmodeled("comparing %v and %v", x, y)
	case x.k == gInt:
		return x.i == y.i
	case x.k == gBool:
		return x.b == y.b
	case x.k == gFloat:
		return x.f == y.f
	case x.k == gOp, x.k == gSym:
		return x.s == y.s
	case x.k == gValue:
		return c.same(x.v, y.v)
	}
	return false
}

func compareInt(a, b int64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func compareUint(a, b uint64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func compareFloat(a, b float64) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

// helperName returns the name of a called function or method, with its
// first letter lowercased: rulegen's helpers were once unexported.
func helperName(fun ast.Expr) string {
	var name string
	switch f := fun.(type) {
	case *ast.Ident:
		name = f.Name
	case *ast.SelectorExpr:
		name = f.Sel.Name
	case *ast.IndexExpr: // explicit instantiation
		return helperName(f.X)
	default:
		return ""
	}
	r, n := utf8.DecodeRuneInString(name)
	return string(unicode.ToLower(r)) + name[n:]
}

// immaterial are helpers whose result doesn't affect what a rule's match
// or result computes, such as use counts and placement.
var immaterial = map[string]bool{
	"clobber": true, "clobberIfDead": true, "canMergeLoad": true, "canMergeLoadClobber": true,
	"canMergeSym": true, "mergeSym": true, "mergePoint": true, "isSamePtr": true,
	"canonLessThan": true, "countRule": true, "is64BitInt": true, "is32BitInt": true,
	"is16BitInt": true, "is8BitInt": true, "isPtr": true, "is64BitFloat": true, "is32BitFloat": true,
	"flagArg": true, "symIsRO": true, "symIsROZero": true, "isInlinableMemmove": true,
	"isInlinableMemclr": true, "logLargeCopy": true, "needRaceCleanup": true, "noteRule": true,
	"warnRule": true, "hasSmallRotate": true, "isSameCall": true, "canLoadUnaligned": true,
	"supportsPPC64PCRel": true,
}

func (c *ctx) call(e *ast.CallExpr, t types.Type) gv {
	if tv := c.info.Types[e.Fun]; tv.IsType() {
		x := c.goExpr(e.Args[0])
		return c.convert(x, tv.Type)
	}
	name := helperName(e.Fun)
	// Methods.
	if sel, ok := e.Fun.(*ast.SelectorExpr); ok && !c.isPkg(sel.X) {
		{
			recv := c.goExpr(sel.X)
			if recv.k == gTop || recv.k == gValue {
				return top
			}
			if r := c.fcMethod(name, recv); r.k != gTop {
				return r
			}
			if r := c.voMethod(name, recv, e); r.k != gTop {
				return r
			}
			if r := ccMaskMethod(name, recv); r.k != gTop {
				return r
			}
			unmodeled("method %s", types.ExprString(e.Fun))
		}
	}
	if immaterial[name] {
		return top
	}
	if name == "shiftIsBounded" {
		return c.shiftIsBounded()
	}
	args := make([]gv, len(e.Args))
	for i, a := range e.Args {
		args[i] = c.goExpr(a)
	}
	for _, a := range args {
		if a.k == gTop {
			return top
		}
	}
	return c.helper(name, args, t, e)
}

func (c *ctx) convert(x gv, t types.Type) gv {
	if x.k == gTop {
		return top
	}
	b := basic(t)
	if b == nil {
		if x.k == gInt || x.k == gOp {
			return gv{k: x.k, i: x.i, s: x.s, t: t}
		}
		unmodeled("conversion to %v", t)
	}
	switch {
	case b.Info()&types.IsInteger != 0:
		switch x.k {
		case gInt:
			return mkInt(x.i, t)
		case gFloat:
			if x.f != x.f || math.IsInf(x.f, 0) {
				impossible()
			}
			if isSigned(t) {
				return mkInt(uint64(int64(x.f)), t)
			}
			return mkInt(uint64(x.f), t)
		}
	case b.Info()&types.IsFloat != 0:
		var f float64
		switch x.k {
		case gInt:
			if isSigned(x.t) {
				f = float64(int64(x.i))
			} else {
				f = float64(x.i)
			}
		case gFloat:
			f = x.f
		default:
			unmodeled("conversion to float")
		}
		if b.Kind() == types.Float32 {
			f = float64(float32(f))
		}
		return gv{k: gFloat, f: f, t: t}
	case b.Info()&types.IsBoolean != 0:
		return x
	}
	unmodeled("conversion of %v to %v", x, t)
	return top
}

// helper evaluates a call of a rewrite helper.
func (c *ctx) helper(name string, args []gv, t types.Type, e *ast.CallExpr) gv {
	i64 := func(k int) int64 {
		if args[k].k != gInt {
			unmodeled("%s argument %v", name, args[k])
		}
		return int64(args[k].i)
	}
	u64 := func(k int) uint64 { return uint64(i64(k)) }
	ret := func(x uint64) gv { return mkInt(x, t) }
	argw := func(k int) uint8 { return width(args[k].t) }
	switch name {
	case "is8Bit":
		return boolGV(i64(0) == int64(int8(i64(0))))
	case "is16Bit":
		return boolGV(i64(0) == int64(int16(i64(0))))
	case "is32Bit":
		return boolGV(i64(0) == int64(int32(i64(0))))
	case "is12Bit":
		return boolGV(-(1<<11) <= i64(0) && i64(0) < 1<<11)
	case "is20Bit":
		return boolGV(-(1<<19) <= i64(0) && i64(0) < 1<<19)
	case "isU8Bit":
		return boolGV(i64(0) == int64(uint8(i64(0))))
	case "isU12Bit":
		return boolGV(0 <= i64(0) && i64(0) < 1<<12)
	case "isU16Bit":
		return boolGV(i64(0) == int64(uint16(i64(0))))
	case "isU32Bit":
		return boolGV(i64(0) == int64(uint32(i64(0))))
	case "isPowerOfTwo", "isPowerOfTwo8", "isPowerOfTwo16", "isPowerOfTwo32", "isPowerOfTwo64":
		// The generic version takes any integer type: n > 0 && n&(n-1) == 0.
		x := args[0]
		if isSigned(x.t) && int64(x.i) <= 0 || x.i == 0 {
			return boolGV(false)
		}
		return boolGV(x.i&(x.i-1) == 0)
	case "isUint64PowerOfTwo":
		return boolGV(u64(0) != 0 && u64(0)&(u64(0)-1) == 0)
	case "isUint32PowerOfTwo":
		x := uint64(uint32(u64(0)))
		return boolGV(x != 0 && x&(x-1) == 0)
	case "oneBit", "oneBit8", "oneBit16", "oneBit32", "oneBit64":
		x := trunc(u64(0), argw(0))
		return boolGV(x != 0 && x&(x-1) == 0)
	case "log2", "log64":
		return ret(uint64(63 - bits.LeadingZeros64(u64(0))))
	case "log8", "log16", "log32", "log8u", "log16u", "log32u", "log64u":
		w := map[string]uint8{"log8": 8, "log16": 16, "log32": 32, "log8u": 8, "log16u": 16, "log32u": 32, "log64u": 64}[name]
		return ret(uint64(63 - bits.LeadingZeros64(trunc(u64(0), w))))
	case "ntz64":
		return ret(uint64(bits.TrailingZeros64(u64(0))))
	case "ntz32":
		return ret(uint64(bits.TrailingZeros32(uint32(u64(0)))))
	case "ntz16":
		return ret(uint64(bits.TrailingZeros16(uint16(u64(0)))))
	case "ntz8":
		return ret(uint64(bits.TrailingZeros8(uint8(u64(0)))))
	case "nlz64":
		return ret(uint64(bits.LeadingZeros64(u64(0))))
	case "nlz32":
		return ret(uint64(bits.LeadingZeros32(uint32(u64(0)))))
	case "nto64":
		return ret(uint64(bits.TrailingZeros64(^u64(0))))
	case "nto32":
		return ret(uint64(bits.TrailingZeros32(^uint32(u64(0)))))
	case "b2i", "b2i32":
		if args[0].k != gBool {
			unmodeled("b2i of %v", args[0])
		}
		return ret(b2u(args[0].b))
	case "zeroUpper32Bits", "zeroUpper48Bits", "zeroUpper56Bits":
		// These report a fact about the value, so they are true only of
		// values with the property.
		w := map[string]uint8{"zeroUpper32Bits": 32, "zeroUpper48Bits": 16, "zeroUpper56Bits": 8}[name]
		v := args[0]
		if v.k != gValue || v.v.k != kInt {
			unmodeled("%s of %v", name, v)
		}
		if v.v.w < 64 {
			// The value's upper bits are undefined: no way to know.
			return boolGV(false)
		}
		return boolGV(v.v.i>>w == 0)
	case "subFlags64", "subFlags32", "addFlags64", "addFlags32", "logicFlags64", "logicFlags32":
		w := uint8(64)
		if strings.HasSuffix(name, "32") {
			w = 32
		}
		f := &flags{w: w, a: u64(0)}
		switch {
		case strings.HasPrefix(name, "sub"):
			f.b = u64(1)
			subFlags(f, false)
		case strings.HasPrefix(name, "add"):
			f.b = u64(1)
			addFlags(f)
		default:
			r := trunc(f.a, w)
			f.setBit(bZ, r == 0)
			f.setBit(bN, sext(r, w) < 0)
			f.setBit(bC, false)
			f.setBit(bV, false)
		}
		return mkInt(encodeFC(f), t)
	case "arm64Negate", "arm64Invert":
		if args[0].k != gOp {
			unmodeled("%s of %v", name, args[0])
		}
		m := arm64Negate
		if name == "arm64Invert" {
			m = arm64Invert
		}
		r, ok := m[args[0].s]
		if !ok {
			impossible() // the helper panics
		}
		return gv{k: gOp, s: r, t: args[0].t}
	case "makeValAndOff":
		return gv{k: gInt, i: uint64(i64(0)<<32 | int64(uint32(i64(1)))), t: t}
	case "ccARM64Eval":
		return ret(uint64(c.ccARM64Eval(args[0], args[1])))
	}
	unmodeled("helper %s", types.ExprString(e.Fun))
	return top
}

// encodeFC encodes the NZCV bits of f as an ssa.FlagConstant.
func encodeFC(f *flags) uint64 {
	var fc uint64
	for i, b := range []bit{bN, bZ, bC, bV} {
		if f.get(b) == tTrue {
			fc |= 1 << i
		}
	}
	return fc
}

// fcMethod evaluates a method of ssa.FlagConstant.
func (c *ctx) fcMethod(name string, recv gv) gv {
	n, ok := recv.t.(*types.Named)
	if !ok || !strings.EqualFold(n.Obj().Name(), "FlagConstant") {
		return top
	}
	f := flagConstant(recv.i)
	cd, ok := fcMethods[name]
	if !ok {
		unmodeled("FlagConstant method %s", name)
	}
	return boolGV(cd(f) == tTrue)
}

// flagConstant returns the flags of an ARM-style ssa.FlagConstant.
func flagConstant(fc uint64) *flags {
	f := &flags{op: "FlagConstant", o: oConst, aux: fc}
	f.setBit(bN, fc&1 != 0)
	f.setBit(bZ, fc&2 != 0)
	f.setBit(bC, fc&4 != 0)
	f.setBit(bV, fc&8 != 0)
	return f
}

// fcMethods are the methods of ssa.FlagConstant (rewrite.go).
var fcMethods = map[string]func(*flags) tri{
	"n":      func(f *flags) tri { return f.get(bN) },
	"z":      func(f *flags) tri { return f.get(bZ) },
	"c":      func(f *flags) tri { return f.get(bC) },
	"v":      func(f *flags) tri { return f.get(bV) },
	"eq":     armEQ,
	"ne":     func(f *flags) tri { return armEQ(f).not() },
	"lt":     armLT,
	"le":     armLE,
	"gt":     func(f *flags) tri { return armLE(f).not() },
	"ge":     func(f *flags) tri { return armLT(f).not() },
	"ult":    func(f *flags) tri { return f.get(bC).not() },
	"ule":    armLS,
	"ugt":    func(f *flags) tri { return armLS(f).not() },
	"uge":    func(f *flags) tri { return f.get(bC) },
	"ltNoov": func(f *flags) tri { return armLT(f).and(f.get(bV).not()) },
	"leNoov": func(f *flags) tri { return armLE(f).and(f.get(bV).not()) },
	"gtNoov": func(f *flags) tri { return armLE(f).not().and(f.get(bV).not()) },
	"geNoov": func(f *flags) tri { return armLT(f).not().and(f.get(bV).not()) },
}

func armEQ(f *flags) tri { return f.get(bZ) }
func armLT(f *flags) tri { return f.get(bNxV) }
func armLE(f *flags) tri { return f.get(bZ).or(f.get(bNxV)) }
func armLS(f *flags) tri { return f.get(bC).not().or(f.get(bZ)) }

// voMethod evaluates a method of ssa.ValAndOff (ssa/op.go).
func (c *ctx) voMethod(name string, recv gv, e *ast.CallExpr) gv {
	n, ok := recv.t.(*types.Named)
	if !ok || n.Obj().Name() != "ValAndOff" {
		return top
	}
	x := int64(recv.i)
	t := c.info.TypeOf(e)
	arg := func() int64 {
		if len(e.Args) != 1 {
			unmodeled("ValAndOff.%s", name)
		}
		a := c.goExpr(e.Args[0])
		if a.k != gInt {
			unmodeled("ValAndOff.%s(%v)", name, a)
		}
		return int64(a.i)
	}
	switch name {
	case "val", "val64", "val16", "val8":
		return mkInt(uint64(x>>32), t)
	case "off", "off64":
		return mkInt(uint64(int64(int32(x))), t)
	case "canAdd32", "canAdd64":
		s := int64(int32(x)) + arg()
		return boolGV(s == int64(int32(s)))
	case "addOffset32", "addOffset64":
		off := int64(int32(x)) + arg()
		if off != int64(int32(off)) {
			impossible() // the method panics
		}
		return gv{k: gInt, i: uint64(x>>32<<32 | int64(uint32(off))), t: recv.t}
	}
	unmodeled("ValAndOff.%s", name)
	return top
}

// shiftIsBounded models ssa.ShiftIsBounded(v), which reports the bounded
// flag of the matched shift: false, or true when the count is known to be
// less than the width.
func (c *ctx) shiftIsBounded() gv {
	r := c.root
	if r == nil {
		unmodeled("shiftIsBounded without a root")
	}
	w, cw, ok := shiftBounds(r.op)
	if !ok || len(r.args) != 2 {
		unmodeled("shiftIsBounded of %s", r.op)
	}
	b := c.choose(2) == 1
	if b && trunc(r.args[1].i, cw) >= uint64(w) {
		impossible()
	}
	return boolGV(b)
}
