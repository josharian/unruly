package gensem

import (
	"fmt"
	"strings"
)

// TypeKind classifies a Type.
type TypeKind uint8

const (
	TInvalid TypeKind = iota
	TInt              // signed integer
	TUint             // unsigned integer, including uintptr
	TFloat
	TBool
	TPtr // pointer-shaped
	TTuple
	TFlags
	TMem
	TVoid
)

// Type models the compiler's *types.Type for the scalar types that rules
// compute with. Types are interned per Universe, so pointer equality is
// type identity, as in the compiler.
type Type struct {
	Name  string // as in the typ struct: "Int64", "UInt8", "Uintptr", ...
	Kind  TypeKind
	Size  int64 // in bytes
	Elems []*Type
}

func (t *Type) String() string { return t.Name }

// Bits returns t's size in bits.
func (t *Type) Bits() int { return int(t.Size * 8) }

func (t *Type) IsInteger() bool { return t.Kind == TInt || t.Kind == TUint }
func (t *Type) IsSigned() bool  { return t.Kind == TInt }
func (t *Type) IsFloat() bool   { return t.Kind == TFloat }
func (t *Type) IsBoolean() bool { return t.Kind == TBool }
func (t *Type) IsPtr() bool     { return t.Kind == TPtr }
func (t *Type) IsTuple() bool   { return t.Kind == TTuple }
func (t *Type) IsFlags() bool   { return t.Kind == TFlags }
func (t *Type) IsMemory() bool  { return t.Kind == TMem }
func (t *Type) IsUintptr() bool { return t.Name == "Uintptr" }

// Universe holds the interned types for one pointer size.
type Universe struct {
	PtrSize int64
	byName  map[string]*Type
	tuples  map[[2]*Type]*Type
	ints    map[[2]int64]*Type // {size, signed} -> type
}

// NewUniverse returns the types of a target with the given pointer size.
func NewUniverse(ptrSize int64) *Universe {
	u := &Universe{PtrSize: ptrSize, byName: map[string]*Type{}, tuples: map[[2]*Type]*Type{}, ints: map[[2]int64]*Type{}}
	add := func(name string, k TypeKind, size int64) {
		u.byName[name] = &Type{Name: name, Kind: k, Size: size}
	}
	for _, s := range []int64{1, 2, 4, 8} {
		add(fmt.Sprintf("Int%d", s*8), TInt, s)
		add(fmt.Sprintf("UInt%d", s*8), TUint, s)
		u.ints[[2]int64{s, 1}] = u.byName[fmt.Sprintf("Int%d", s*8)]
		u.ints[[2]int64{s, 0}] = u.byName[fmt.Sprintf("UInt%d", s*8)]
	}
	add("Int", TInt, ptrSize)
	add("UInt", TUint, ptrSize)
	add("Uintptr", TUint, ptrSize)
	add("Float32", TFloat, 4)
	add("Float64", TFloat, 8)
	add("Bool", TBool, 1)
	add("BytePtr", TPtr, ptrSize)
	add("Int64Ptr", TPtr, ptrSize) // another pointer type, like *int64
	add("Flags", TFlags, 0)
	add("Mem", TMem, 0)
	add("Void", TVoid, 0)
	// Aliases used in some op tables and rules.
	u.byName["Uint32"] = u.byName["UInt32"]
	u.byName["Uint64"] = u.byName["UInt64"]
	u.byName["Uint8"] = u.byName["UInt8"]
	return u
}

// Named returns the type for a name as used in an op's default type
// ("UInt64", "(UInt32,Flags)") or a field of the typ struct, or nil.
func (u *Universe) Named(name string) *Type {
	name = strings.TrimSpace(name)
	if strings.HasPrefix(name, "(") && strings.HasSuffix(name, ")") {
		parts := strings.Split(name[1:len(name)-1], ",")
		if len(parts) != 2 {
			return nil
		}
		a, b := u.Named(parts[0]), u.Named(parts[1])
		if a == nil || b == nil {
			return nil
		}
		return u.Tuple(a, b)
	}
	return u.byName[name]
}

// Int returns the integer type of the given size in bytes and signedness.
func (u *Universe) Int(size int64, signed bool) *Type {
	s := int64(0)
	if signed {
		s = 1
	}
	return u.ints[[2]int64{size, s}]
}

// Tuple returns the tuple type (a, b).
func (u *Universe) Tuple(a, b *Type) *Type {
	k := [2]*Type{a, b}
	if t := u.tuples[k]; t != nil {
		return t
	}
	t := &Type{Name: "(" + a.Name + "," + b.Name + ")", Kind: TTuple, Elems: []*Type{a, b}}
	u.tuples[k] = t
	return t
}

// kindNames maps the compiler's types.Kind constant names (types.TINT64)
// to type names, for types.Types[types.TXXX].
var kindNames = map[string]string{
	"TINT8": "Int8", "TUINT8": "UInt8", "TINT16": "Int16", "TUINT16": "UInt16",
	"TINT32": "Int32", "TUINT32": "UInt32", "TINT64": "Int64", "TUINT64": "UInt64",
	"TINT": "Int", "TUINT": "UInt", "TUINTPTR": "Uintptr",
	"TFLOAT32": "Float32", "TFLOAT64": "Float64", "TBOOL": "Bool",
}

// ByKindName returns the type for a types.Kind constant name such as
// "TUINT64", or nil.
func (u *Universe) ByKindName(name string) *Type {
	if n, ok := kindNames[name]; ok {
		return u.byName[n]
	}
	return nil
}
