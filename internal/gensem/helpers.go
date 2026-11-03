package gensem

import (
	"fmt"
	"go/types"
	"math"
	"math/bits"
	"strings"
)

// helpers are the functions that rules call, keyed by helperKey.
//
// Pure helpers are copied from the compiler (cmd/compile/internal/ssa's
// rewrite.go and magic.go, and the rewrite/<arch>/*_helpers.go files);
// see GOLICENSE in package rules. Helpers that inspect values (such as
// isNonNegative) are reimplemented on Value. Helpers that only gate
// whether a rewrite is profitable on some arch return what the compiler
// returns for Env.Cfg. Anything else is unsupported, and rules that reach
// it are not evaluated.
type helper func(e *Env, args []GoVal, t types.Type) (GoVal, error)

var helpers = map[string]helper{}

func init() {
	i64 := func(g GoVal) int64 { return int64(g.I) }
	u64 := func(g GoVal) uint64 { return g.I & mask(intBits(g.T)) }
	boolf := func(f func(args []GoVal) bool) helper {
		return func(_ *Env, args []GoVal, t types.Type) (GoVal, error) { return mkBool(t, f(args)), nil }
	}
	intf := func(f func(args []GoVal) int64) helper {
		return func(_ *Env, args []GoVal, t types.Type) (GoVal, error) { return mkInt(t, uint64(f(args))), nil }
	}

	helpers["is32Bit"] = boolf(func(a []GoVal) bool { n := i64(a[0]); return n == int64(int32(n)) })
	helpers["is16Bit"] = boolf(func(a []GoVal) bool { n := i64(a[0]); return n == int64(int16(n)) })
	helpers["isU32Bit"] = boolf(func(a []GoVal) bool { n := i64(a[0]); return uint64(n) == uint64(uint32(n)) })
	helpers["isU16Bit"] = boolf(func(a []GoVal) bool { n := i64(a[0]); return uint64(n) == uint64(uint16(n)) })
	helpers["isU8Bit"] = boolf(func(a []GoVal) bool { n := i64(a[0]); return uint64(n) == uint64(uint8(n)) })

	// isPowerOfTwo is generic over integer types in newer trees and
	// takes an int64 in older ones; either way, the arg's own type decides.
	pow2 := boolf(func(a []GoVal) bool {
		n := a[0]
		if isUnsigned(n.T) {
			return n.I != 0 && n.I&(n.I-1) == 0
		}
		return int64(n.I) > 0 && n.I&(n.I-1) == 0
	})
	for _, name := range []string{"isPowerOfTwo", "isPowerOfTwo8", "isPowerOfTwo16", "isPowerOfTwo32", "isPowerOfTwo64", "isUnsignedPowerOfTwo"} {
		helpers[name] = pow2
	}
	helpers["isUint64PowerOfTwo"] = boolf(func(a []GoVal) bool { n := uint64(i64(a[0])); return n != 0 && n&(n-1) == 0 })
	helpers["isUint32PowerOfTwo"] = boolf(func(a []GoVal) bool { n := uint64(uint32(i64(a[0]))); return n != 0 && n&(n-1) == 0 })
	// oneBit reports whether x contains exactly one set bit.
	oneBit := boolf(func(a []GoVal) bool { x := u64(a[0]); return x != 0 && x&(x-1) == 0 })
	for _, name := range []string{"oneBit", "oneBit8", "oneBit16", "oneBit32", "oneBit64"} {
		helpers[name] = oneBit
	}

	logu := func(a []GoVal) int64 { return int64(bits.Len64(u64(a[0]))) - 1 }
	for _, name := range []string{"log8", "log16", "log32", "log64", "log8u", "log16u", "log32u", "log64u", "log2", "log2uint32"} {
		helpers[name] = intf(logu)
	}
	for _, w := range []int{8, 16, 32, 64} {
		w := w
		helpers[fmt.Sprintf("ntz%d", w)] = intf(func(a []GoVal) int64 { return int64(min(bits.TrailingZeros64(u64(a[0])), w)) })
		helpers[fmt.Sprintf("nlz%d", w)] = intf(func(a []GoVal) int64 { return int64(bits.LeadingZeros64(u64(a[0])) - (64 - w)) })
		helpers[fmt.Sprintf("nto%d", w)] = intf(func(a []GoVal) int64 { return int64(min(bits.TrailingZeros64(^u64(a[0])), w)) })
	}
	helpers["uaddOvf"] = boolf(func(a []GoVal) bool { return a[0].I+a[1].I < a[0].I })
	helpers["bool2int"] = intf(func(a []GoVal) int64 { return int64(a[0].I) })
	helpers["b2i"] = helpers["bool2int"]
	helpers["b2i32"] = helpers["bool2int"]

	// Magic numbers for division by constants (magic.go).
	for _, w := range []uint{8, 16, 32, 64} {
		w := w
		helpers[fmt.Sprintf("umagicOK%d", w)] = boolf(func(a []GoVal) bool { c := u64(a[0]); return c&(c-1)&mask(int(w)) != 0 })
		helpers[fmt.Sprintf("smagicOK%d", w)] = boolf(func(a []GoVal) bool { return smagicOK(w, i64(a[0])) })
		helpers[fmt.Sprintf("udivisibleOK%d", w)] = boolf(func(a []GoVal) bool { return udivisibleOK(w, i64(a[0])) })
		helpers[fmt.Sprintf("sdivisibleOK%d", w)] = boolf(func(a []GoVal) bool { return smagicOK(w, i64(a[0])) })
		helpers[fmt.Sprintf("umagic%d", w)] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			return magicStruct(t, func() map[string]uint64 { return umagic(w, i64(a[0])) })
		}
		helpers[fmt.Sprintf("smagic%d", w)] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			return magicStruct(t, func() map[string]uint64 { return smagic(w, i64(a[0])) })
		}
		helpers[fmt.Sprintf("udivisible%d", w)] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			return magicStruct(t, func() map[string]uint64 { return udivisible(w, i64(a[0])) })
		}
		helpers[fmt.Sprintf("sdivisible%d", w)] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			return magicStruct(t, func() map[string]uint64 { return sdivisible(w, i64(a[0])) })
		}
	}
	nc := func(f func(n uint, c int64) map[string]uint64) helper {
		return func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			return magicStruct(t, func() map[string]uint64 { return f(uint(a[0].I), i64(a[1])) })
		}
	}
	helpers["umagic"] = nc(umagic)
	helpers["smagic"] = nc(smagic)
	helpers["udivisible"] = nc(udivisible)
	helpers["sdivisible"] = nc(sdivisible)
	helpers["umagicOK"] = boolf(func(a []GoVal) bool { return udivisibleOK(uint(a[0].I), i64(a[1])) })
	helpers["smagicOK"] = boolf(func(a []GoVal) bool { return smagicOK(uint(a[0].I), i64(a[1])) })
	helpers["udivisibleOK"] = boolf(func(a []GoVal) bool { return udivisibleOK(uint(a[0].I), i64(a[1])) })
	helpers["sdivisibleOK"] = boolf(func(a []GoVal) bool { return smagicOK(uint(a[0].I), i64(a[1])) })
	helpers["umagic32PreShifted"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		var m map[string]uint64
		if err := catch(func() { m = umagic(32, i64(a[0])) }); err != nil {
			return GoVal{}, err
		}
		return mkInt(t, (1<<32+m["M"])<<uint(32-int64(m["S"]))), nil
	}
	helpers["modularMultiplicativeInverse"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		x := a[0].I
		if x%2 != 1 {
			return GoVal{}, &Panic{"even numbers in a power-of-two modulus do not have a multiplicative inverse"}
		}
		y := x
		for range 5 {
			y *= 2 - x*y
		}
		return mkInt(t, y), nil
	}

	// math/bits results packaged in structs (generic_helpers.go).
	pair := func(f func(a []GoVal) (uint64, uint64, error), names ...string) helper {
		return func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			x, y, err := f(a)
			if err != nil {
				return GoVal{}, err
			}
			return magicStruct(t, func() map[string]uint64 { return map[string]uint64{names[0]: x, names[1]: y} })
		}
	}
	helpers["bitsAdd64"] = pair(func(a []GoVal) (uint64, uint64, error) {
		s, c := bits.Add64(a[0].I, a[1].I, a[2].I)
		return s, c, nil
	}, "sum", "carry")
	helpers["bitsSub64"] = pair(func(a []GoVal) (uint64, uint64, error) {
		d, b := bits.Sub64(a[0].I, a[1].I, a[2].I)
		return d, b, nil
	}, "diff", "borrow")
	helpers["bitsMulU64"] = pair(func(a []GoVal) (uint64, uint64, error) {
		hi, lo := bits.Mul64(a[0].I, a[1].I)
		return hi, lo, nil
	}, "hi", "lo")
	helpers["bitsMulU32"] = pair(func(a []GoVal) (uint64, uint64, error) {
		hi, lo := bits.Mul32(uint32(a[0].I), uint32(a[1].I))
		return uint64(hi), uint64(lo), nil
	}, "hi", "lo")
	helpers["bitsDiv128u"] = pair(func(a []GoVal) (uint64, uint64, error) {
		hi, lo, y := a[0].I, a[1].I, a[2].I
		if y == 0 {
			return 0, 0, &Panic{"integer divide by zero"}
		}
		if y <= hi {
			return 0, 0, &Panic{"integer overflow"}
		}
		q, r := bits.Div64(hi, lo, y)
		return q, r, nil
	}, "quo", "rem")

	helpers["reciprocalExact64"] = boolf(func(a []GoVal) bool {
		b := math.Float64bits(a[0].F)
		if b&(1<<52-1) != 0 {
			return false
		}
		switch b >> 52 & (1<<11 - 1) {
		case 0, 0x7ff, 0x7fe:
			return false
		}
		return true
	})
	helpers["reciprocalExact32"] = boolf(func(a []GoVal) bool {
		b := math.Float32bits(float32(a[0].F))
		if b&(1<<23-1) != 0 {
			return false
		}
		switch b >> 23 & (1<<8 - 1) {
		case 0, 0xff, 0xfe:
			return false
		}
		return true
	})

	// Type predicates (rewrite.go).
	typePred := func(f func(t *Type) bool) helper {
		return func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
			ty, _ := a[0].X.(*Type)
			if ty == nil {
				return GoVal{}, unsupported("type predicate of non-type")
			}
			return mkBool(t, f(ty)), nil
		}
	}
	helpers["is8BitInt"] = typePred(func(t *Type) bool { return t.Size == 1 && t.IsInteger() })
	helpers["is16BitInt"] = typePred(func(t *Type) bool { return t.Size == 2 && t.IsInteger() })
	helpers["is32BitInt"] = typePred(func(t *Type) bool { return t.Size == 4 && t.IsInteger() })
	helpers["is64BitInt"] = typePred(func(t *Type) bool { return t.Size == 8 && t.IsInteger() })
	helpers["is32BitFloat"] = typePred(func(t *Type) bool { return t.Size == 4 && t.IsFloat() })
	helpers["is64BitFloat"] = typePred(func(t *Type) bool { return t.Size == 8 && t.IsFloat() })
	helpers["isPtr"] = typePred(func(t *Type) bool { return t.IsPtr() })

	// Value inspection.
	helpers["isNonNegative"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		v, _ := a[0].X.(*Value)
		if v == nil {
			return GoVal{}, unsupported("isNonNegative of non-value")
		}
		if v.Type == nil || !v.Type.IsInteger() {
			return GoVal{}, &Panic{fmt.Sprintf("isNonNegative bad type: %v", v.Type)}
		}
		return mkBool(t, isNonNegative(v)), nil
	}
	helpers["isSamePtr"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		p1, _ := a[0].X.(*Value)
		p2, _ := a[1].X.(*Value)
		if p1 == nil || p2 == nil {
			return GoVal{}, unsupported("isSamePtr of non-values")
		}
		return mkBool(t, isSamePtr(p1, p2)), nil
	}
	helpers["shiftIsBounded"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		v, _ := a[0].X.(*Value)
		if v == nil {
			return GoVal{}, unsupported("shiftIsBounded of non-value")
		}
		return mkBool(t, v.AuxInt != 0), nil
	}
	// clobber and friends only update use counts; they report true.
	alwaysTrue := func(_ *Env, _ []GoVal, t types.Type) (GoVal, error) { return mkBool(t, true), nil }
	helpers["clobber"] = alwaysTrue
	helpers["clobberIfDead"] = alwaysTrue
	helpers["warnRule"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) { return mkBool(t, true), nil }
	// canonLessThan picks a canonical order of commutative args by op and
	// value ID; rules guarded by it must be correct either way.
	helpers["canonLessThan"] = alwaysTrue

	// Profitability gates (generic_helpers.go).
	helpers["canRotate"] = func(e *Env, a []GoVal, t types.Type) (GoVal, error) {
		n := i64(a[1])
		c := e.Cfg
		if n > c.RegSize*8 {
			return mkBool(t, false), nil
		}
		switch c.Arch {
		case "386", "amd64", "arm64", "loong64", "riscv64":
			return mkBool(t, true), nil
		case "arm", "s390x", "ppc64", "ppc64le", "wasm":
			return mkBool(t, n >= 32), nil
		}
		return mkBool(t, false), nil
	}
	helpers["hasSmallRotate"] = func(e *Env, a []GoVal, t types.Type) (GoVal, error) {
		return mkBool(t, e.Cfg.Arch == "amd64" || e.Cfg.Arch == "386"), nil
	}
	helpers["rewriteCondSelectIntoMath"] = func(e *Env, a []GoVal, t types.Type) (GoVal, error) {
		op, _ := a[1].X.(Op)
		c := a[2].I
		pow2 := c != 0 && c&(c-1) == 0
		if e.Cfg.Arch == "arm64" && strings.HasPrefix(string(op), "Add") && c == 1 {
			return mkBool(t, false), nil
		}
		return mkBool(t, pow2), nil
	}
	helpers["addToSub"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		op, _ := a[0].X.(Op)
		switch op {
		case "Add64", "Add32", "Add16", "Add8":
			return GoVal{T: t, X: Op("Sub" + string(op)[3:])}, nil
		}
		return GoVal{}, &Panic{fmt.Sprintf("unexpected op %v", op)}
	}
	helpers["invertibleBool"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		op, _ := a[0].X.(Op)
		return mkBool(t, invertibleBool[op]), nil
	}

	// math and math/bits.
	f1 := func(f func(float64) float64) helper {
		return func(_ *Env, a []GoVal, t types.Type) (GoVal, error) { return mkFloat(t, f(a[0].F)), nil }
	}
	helpers["math.Sqrt"] = f1(math.Sqrt)
	helpers["math.Floor"] = f1(math.Floor)
	helpers["math.Ceil"] = f1(math.Ceil)
	helpers["math.Trunc"] = f1(math.Trunc)
	helpers["math.Round"] = f1(math.Round)
	helpers["math.RoundToEven"] = f1(math.RoundToEven)
	helpers["math.Abs"] = f1(math.Abs)
	helpers["math.Copysign"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		return mkFloat(t, math.Copysign(a[0].F, a[1].F)), nil
	}
	helpers["math.FMA"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		return mkFloat(t, math.FMA(a[0].F, a[1].F, a[2].F)), nil
	}
	helpers["math.IsNaN"] = boolf(func(a []GoVal) bool { return math.IsNaN(a[0].F) })
	helpers["math.Signbit"] = boolf(func(a []GoVal) bool { return math.Signbit(a[0].F) })
	helpers["math.IsInf"] = boolf(func(a []GoVal) bool { return math.IsInf(a[0].F, int(int64(a[1].I))) })
	helpers["math.Float64bits"] = intf(func(a []GoVal) int64 { return int64(math.Float64bits(a[0].F)) })
	helpers["math.Float32bits"] = intf(func(a []GoVal) int64 { return int64(math.Float32bits(float32(a[0].F))) })
	helpers["math.Float64frombits"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		return mkFloat(t, math.Float64frombits(a[0].I)), nil
	}
	helpers["math.Float32frombits"] = func(_ *Env, a []GoVal, t types.Type) (GoVal, error) {
		return mkFloat(t, float64(math.Float32frombits(uint32(a[0].I)))), nil
	}
	for _, w := range []int{8, 16, 32, 64} {
		w := w
		sfx := fmt.Sprint(w)
		helpers["bits.Len"+sfx] = intf(func(a []GoVal) int64 { return int64(bits.Len64(u64(a[0]))) })
		helpers["bits.OnesCount"+sfx] = intf(func(a []GoVal) int64 { return int64(bits.OnesCount64(u64(a[0]))) })
		helpers["bits.TrailingZeros"+sfx] = intf(func(a []GoVal) int64 { return int64(min(bits.TrailingZeros64(u64(a[0])), w)) })
		helpers["bits.LeadingZeros"+sfx] = intf(func(a []GoVal) int64 { return int64(bits.LeadingZeros64(u64(a[0])) - (64 - w)) })
		helpers["bits.Reverse"+sfx] = intf(func(a []GoVal) int64 { return int64(bits.Reverse64(u64(a[0])) >> (64 - w)) })
		if w > 8 {
			helpers["bits.ReverseBytes"+sfx] = intf(func(a []GoVal) int64 { return int64(bits.ReverseBytes64(u64(a[0])) >> (64 - w)) })
		}
		helpers["bits.RotateLeft"+sfx] = intf(func(a []GoVal) int64 {
			x, k := u64(a[0]), uint(int64(a[1].I))&uint(w-1)
			return int64((x<<k | x>>(uint(w)-k)) & mask(w))
		})
	}
}

// invertibleBool is the set of ops for which the compiler's
// invertibleBool (generic_helpers.go) reports true.
var invertibleBool = func() map[Op]bool {
	m := map[Op]bool{"Not": true}
	for _, w := range []string{"64", "32", "16", "8"} {
		for _, op := range []string{"Less", "Leq"} {
			m[Op(op+w)] = true
			m[Op(op+w+"U")] = true
		}
		m[Op("Eq"+w)] = true
		m[Op("Neq"+w)] = true
	}
	return m
}()

// catch runs f, converting a panic into a *Panic.
func catch(f func()) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = &Panic{fmt.Sprint(r)}
		}
	}()
	f()
	return nil
}

// magicStruct builds a value of struct type t from fields computed by f,
// matching field names case-insensitively (newer trees export them).
func magicStruct(t types.Type, f func() map[string]uint64) (GoVal, error) {
	var m map[string]uint64
	if err := catch(func() { m = f() }); err != nil {
		return GoVal{}, err
	}
	st, ok := t.Underlying().(*types.Struct)
	if !ok {
		return GoVal{}, unsupported("helper result %v", t)
	}
	fields := structFields{}
	for i := range st.NumFields() {
		fv := st.Field(i)
		var x uint64
		found := false
		for k, val := range m {
			if strings.EqualFold(k, fv.Name()) {
				x, found = val, true
			}
		}
		if !found {
			return GoVal{}, unsupported("field %s of %v", fv.Name(), t)
		}
		fields[fv.Name()] = mkInt(fv.Type(), x)
	}
	return GoVal{T: t, X: fields}, nil
}

// isSamePtr is the compiler's IsSamePtr (rewrite.go).
func isSamePtr(p1, p2 *Value) bool {
	if p1 == p2 {
		return true
	}
	if p1.OpName() != p2.OpName() {
		for p1.OpName() == "OffPtr" && p1.AuxInt == 0 {
			p1 = p1.Args[0]
		}
		for p2.OpName() == "OffPtr" && p2.AuxInt == 0 {
			p2 = p2.Args[0]
		}
		if p1 == p2 {
			return true
		}
		if p1.OpName() != p2.OpName() {
			return false
		}
	}
	switch p1.OpName() {
	case "OffPtr":
		return p1.AuxInt == p2.AuxInt && isSamePtr(p1.Args[0], p2.Args[0])
	case "Addr", "LocalAddr":
		return p1.Aux == p2.Aux
	case "AddPtr":
		return p1.Args[1] == p2.Args[1] && isSamePtr(p1.Args[0], p2.Args[0])
	}
	return false
}

// isNonNegative is the compiler's isNonNegative (generic_helpers.go).
// It reports whether v is known to be non-negative from its form alone.
func isNonNegative(v *Value) bool {
	switch op := v.OpName(); op {
	case "Const64":
		return v.AuxInt >= 0
	case "Const32":
		return int32(v.AuxInt) >= 0
	case "Const16":
		return int16(v.AuxInt) >= 0
	case "Const8":
		return int8(v.AuxInt) >= 0
	case "StringLen", "SliceLen", "SliceCap",
		"ZeroExt8to64", "ZeroExt16to64", "ZeroExt32to64",
		"ZeroExt8to32", "ZeroExt16to32", "ZeroExt8to16",
		"Ctz64", "Ctz32", "Ctz16", "Ctz8",
		"Ctz64NonZero", "Ctz32NonZero", "Ctz16NonZero", "Ctz8NonZero",
		"BitLen64", "BitLen32", "BitLen16", "BitLen8":
		return true
	case "Rsh64Ux64", "Rsh32Ux64":
		by := v.Args[1]
		return by.OpName() == "Const64" && by.AuxInt > 0
	case "Rsh64x64", "Rsh32x64", "Rsh8x64", "Rsh16x64", "Rsh32x32", "Rsh64x32",
		"SignExt32to64", "SignExt16to64", "SignExt8to64", "SignExt16to32", "SignExt8to32":
		return isNonNegative(v.Args[0])
	case "And64", "And32", "And16", "And8":
		return isNonNegative(v.Args[0]) || isNonNegative(v.Args[1])
	case "Mod64", "Mod32", "Mod16", "Mod8",
		"Div64", "Div32", "Div16", "Div8",
		"Or64", "Or32", "Or16", "Or8",
		"Xor64", "Xor32", "Xor16", "Xor8":
		return isNonNegative(v.Args[0]) && isNonNegative(v.Args[1])
	}
	return false
}
