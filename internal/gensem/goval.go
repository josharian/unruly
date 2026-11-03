package gensem

import (
	"fmt"
	"go/constant"
	"go/types"
	"math"
	"strings"
)

// GoVal is the value of a Go expression in a rule.
type GoVal struct {
	T types.Type
	I uint64  // integers (sign- or zero-extended per T) and bools (0 or 1)
	F float64 // floats (a float32 is held exactly)
	S string
	// X holds everything else: *Value, *Type, *Config, Op, []*Value,
	// structFields, and the markers typStruct and typesArray.
	X any
}

// Op is the value of an ssa.Op: a qualified op name ("Const64",
// "AMD64ADDQ"), or "" for OpInvalid.
type Op string

type structFields map[string]GoVal

type typStruct struct{}   // the typ variable (*ssa.Types)
type blockRef struct{}    // v.Block or b
type funcRef struct{}     // v.Block.Func
type passRef struct{}     // v.Block.Func.Pass
type ctxtRef struct{}     // config.Ctxt
type ctxtArchRef struct{} // config.Ctxt.Arch
type typesArray struct{}  // types.Types

func (g GoVal) String() string {
	switch x := g.X.(type) {
	case nil:
	case *Value:
		return "value"
	case *Type:
		return x.String()
	case Op:
		return "Op" + string(x)
	default:
		return fmt.Sprint(x)
	}
	switch basicInfo(g.T) {
	case infoInt:
		if isUnsigned(g.T) {
			return fmt.Sprint(g.I)
		}
		return fmt.Sprint(int64(g.I))
	case infoFloat:
		return fmt.Sprint(g.F)
	case infoBool:
		return fmt.Sprint(g.I != 0)
	case infoString:
		return fmt.Sprintf("%q", g.S)
	}
	return "nil"
}

type info uint8

const (
	infoOther info = iota
	infoInt
	infoFloat
	infoBool
	infoString
)

func basicInfo(t types.Type) info {
	if t == nil {
		return infoOther
	}
	b, ok := t.Underlying().(*types.Basic)
	if !ok {
		return infoOther
	}
	switch {
	case b.Info()&types.IsInteger != 0:
		return infoInt
	case b.Info()&types.IsFloat != 0:
		return infoFloat
	case b.Info()&types.IsBoolean != 0:
		return infoBool
	case b.Info()&types.IsString != 0:
		return infoString
	}
	return infoOther
}

func isUnsigned(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	return ok && b.Info()&types.IsUnsigned != 0
}

// intBits returns the width of integer type t in the compiler's own Go
// code (a 64-bit host).
func intBits(t types.Type) int {
	b, ok := t.Underlying().(*types.Basic)
	if !ok {
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

func isFloat32(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	return ok && b.Kind() == types.Float32
}

// normInt normalizes x to integer type t.
func normInt(t types.Type, x uint64) uint64 {
	w := intBits(t)
	if isUnsigned(t) {
		return x & mask(w)
	}
	return uint64(sext(x, w))
}

func mkInt(t types.Type, x uint64) GoVal { return GoVal{T: t, I: normInt(t, x)} }

func mkFloat(t types.Type, f float64) GoVal {
	if isFloat32(t) {
		f = float64(float32(f))
	}
	return GoVal{T: t, F: f}
}

func mkBool(t types.Type, b bool) GoVal {
	if t == nil {
		t = types.Typ[types.Bool]
	}
	g := GoVal{T: t}
	if b {
		g.I = 1
	}
	return g
}

// defaultType returns the default type of an untyped type.
func defaultType(t types.Type) types.Type {
	if b, ok := t.(*types.Basic); ok && b.Info()&types.IsUntyped != 0 {
		switch b.Kind() {
		case types.UntypedBool:
			return types.Typ[types.Bool]
		case types.UntypedInt, types.UntypedRune:
			return types.Typ[types.Int64]
		case types.UntypedFloat:
			return types.Typ[types.Float64]
		case types.UntypedString:
			return types.Typ[types.String]
		}
	}
	return t
}

// fromConstant converts a constant of type t to a GoVal.
func fromConstant(c constant.Value, t types.Type) (GoVal, error) {
	t = defaultType(t)
	switch basicInfo(t) {
	case infoInt:
		c = constant.ToInt(c)
		if c.Kind() != constant.Int {
			return GoVal{}, unsupported("constant %v", c)
		}
		if u, ok := constant.Uint64Val(c); ok {
			return mkInt(t, u), nil
		}
		if i, ok := constant.Int64Val(c); ok {
			return mkInt(t, uint64(i)), nil
		}
		return GoVal{}, unsupported("constant %v", c)
	case infoFloat:
		f, _ := constant.Float64Val(constant.ToFloat(c))
		return mkFloat(t, f), nil
	case infoBool:
		return mkBool(t, constant.BoolVal(c)), nil
	case infoString:
		return GoVal{T: t, S: constant.StringVal(c)}, nil
	}
	return GoVal{}, unsupported("constant of type %v", t)
}

// convert converts x to type t, as a Go conversion t(x).
func convert(x GoVal, t types.Type) (GoVal, error) {
	switch to, from := basicInfo(t), basicInfo(x.T); {
	case to == infoInt && from == infoInt:
		return mkInt(t, x.I), nil
	case to == infoFloat && from == infoInt:
		if isUnsigned(x.T) {
			return mkFloat(t, float64(x.I)), nil
		}
		if isFloat32(t) {
			return mkFloat(t, float64(float32(int64(x.I)))), nil
		}
		return mkFloat(t, float64(int64(x.I))), nil
	case to == infoFloat && from == infoFloat:
		return mkFloat(t, x.F), nil
	case to == infoInt && from == infoFloat:
		f := math.Trunc(x.F)
		w := intBits(t)
		lo, hi := -math.Ldexp(1, w-1), math.Ldexp(1, w-1)
		if isUnsigned(t) {
			lo, hi = 0, math.Ldexp(1, w)
		}
		if math.IsNaN(f) || f < lo || f >= hi {
			return GoVal{}, &HostDependent{fmt.Sprintf("converting %v to %v", x.F, t)}
		}
		if isUnsigned(t) {
			return mkInt(t, uint64(f)), nil
		}
		return mkInt(t, uint64(int64(f))), nil
	case to == infoBool && from == infoBool:
		return GoVal{T: t, I: x.I}, nil
	}
	// Conversions between named and unnamed versions of other types,
	// such as ssa.Op(x): keep the payload.
	if basicInfo(t) == infoOther {
		x.T = t
		return x, nil
	}
	return GoVal{}, unsupported("conversion from %v to %v", x.T, t)
}

// HostDependent reports a Go operation whose result depends on the
// machine the compiler runs on, such as converting an out-of-range float
// to an integer. The compiler's output would then depend on its host.
type HostDependent struct{ Msg string }

func (e *HostDependent) Error() string { return "host-dependent: " + e.Msg }

func lowerFirst(s string) string {
	if s == "" {
		return s
	}
	return strings.ToLower(s[:1]) + s[1:]
}
