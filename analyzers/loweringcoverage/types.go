package loweringcoverage

import "fmt"

// A typ models a *types.Type of the compiler, as far as lowering
// conditions inspect it. The predicates mirror cmd/compile/internal/types
// (type.go): IsInteger is true for the integer kinds, IsPtrShaped for
// pointers, unsafe.Pointer, maps, chans, and funcs, and so on. SIMD
// vector and mask types are structs with the SIMD flag set (types/size.go).
type typ struct {
	name  string // for messages, such as "int32" or "struct{ p *T }"
	kind  tkind
	size  int64 // -1 if unknown
	align int64 // -1 if unknown
	simd  bool
	elem  *typ // for pointers
	ptrs  tri  // HasPointers
}

type tkind uint8

const (
	tUnknown tkind = iota
	tInt
	tUint
	tBool
	tFloat
	tPtr       // *T
	tUnsafePtr // unsafe.Pointer
	tStruct
	tArray
	tMem
	tFlags
)

func (t *typ) String() string { return t.name }

// method evaluates the niladic method m of t.
func (t *typ) method(m string) val {
	known := t.kind != tUnknown
	b := func(x bool) val {
		if !known {
			return unknown
		}
		return boolVal(x)
	}
	switch m {
	case "Size":
		if t.size < 0 {
			return unknown
		}
		return intVal(t.size)
	case "Alignment":
		if t.align < 0 {
			return unknown
		}
		return intVal(t.align)
	case "IsInteger":
		return b(t.kind == tInt || t.kind == tUint)
	case "IsSigned":
		return b(t.kind == tInt)
	case "IsUnsigned":
		return b(t.kind == tUint)
	case "IsBoolean":
		return b(t.kind == tBool)
	case "IsFloat":
		return b(t.kind == tFloat)
	case "IsComplex", "IsString", "IsSlice", "IsInterface", "IsTuple", "IsResults", "IsVoid":
		return b(false)
	case "IsPtr":
		return b(t.kind == tPtr)
	case "IsUnsafePtr":
		return b(t.kind == tUnsafePtr)
	case "IsPtrShaped":
		return b(t.kind == tPtr || t.kind == tUnsafePtr)
	case "IsStruct":
		return b(t.kind == tStruct)
	case "IsArray":
		return b(t.kind == tArray)
	case "IsMemory":
		return b(t.kind == tMem)
	case "IsFlags":
		return b(t.kind == tFlags)
	case "IsSIMD":
		return b(t.simd)
	case "HasPointers":
		return t.ptrs.val()
	case "Elem":
		if t.elem == nil {
			return unknown
		}
		return typVal(t.elem)
	}
	return unknown
}

func intType(name string, size int64, signed bool) *typ {
	k := tUint
	if signed {
		k = tInt
	}
	return &typ{name: name, kind: k, size: size, align: size, ptrs: no}
}

// typNames gives the types named by typ.X in rules (ssa.Types in
// cmd/compile/internal/ssa/config.go), for a pointer size.
func typNames(ptrSize int64) map[string]*typ {
	byteT := intType("uint8", 1, false)
	m := map[string]*typ{
		"Int8":    intType("int8", 1, true),
		"Int16":   intType("int16", 2, true),
		"Int32":   intType("int32", 4, true),
		"Int64":   intType("int64", 8, true),
		"UInt8":   byteT,
		"UInt16":  intType("uint16", 2, false),
		"UInt32":  intType("uint32", 4, false),
		"UInt64":  intType("uint64", 8, false),
		"Int":     intType("int", ptrSize, true),
		"UInt":    intType("uint", ptrSize, false),
		"Uintptr": intType("uintptr", ptrSize, false),
		"Bool":    {name: "bool", kind: tBool, size: 1, align: 1, ptrs: no},
		"Float32": {name: "float32", kind: tFloat, size: 4, align: 4, ptrs: no},
		"Float64": {name: "float64", kind: tFloat, size: 8, align: 8, ptrs: no},
	}
	if ptrSize == 4 {
		m["Int64"].align = 4
		m["UInt64"].align = 4
		m["Float64"].align = 4
	}
	for _, n := range []string{"Int8", "Int16", "Int32", "Int64", "UInt8", "UInt16", "UInt32", "UInt64", "Int", "Uintptr", "Float32", "Float64"} {
		e := m[n]
		pn := map[string]string{"UInt8": "BytePtr", "UInt32": "UInt32Ptr", "Int": "IntPtr"}[n]
		if pn == "" {
			pn = n + "Ptr"
		}
		m[pn] = ptrTo(e, ptrSize)
	}
	m["BytePtrPtr"] = ptrTo(m["BytePtr"], ptrSize)
	return m
}

func ptrTo(e *typ, ptrSize int64) *typ {
	return &typ{name: "*" + e.name, kind: tPtr, size: ptrSize, align: ptrSize, elem: e, ptrs: yes}
}

// valueTypes returns the types of SSA values that can reach the lower
// pass as the type of a Load or the aux type of a Store, on an arch with
// the given pointer size.
//
// Composite and 64-bit-on-32-bit types are excluded because the
// "decompose builtin", "decompose user", and "dec64" passes split them
// first: dec.rules rewrites every SSA-able struct and array Load into a
// StructMake/ArrayMake of field loads, and dec64.rules splits Int64 loads
// and stores on 32-bit arches. A Store's value, though, can still be a
// struct of one pointer that no StructMake produced (as for direct
// interface data under the register ABI, test/fixedbugs/issue45344.go),
// so the Store universe also includes struct{ p *T }.
func valueTypes(ptrSize int64, store bool) []*typ {
	n := typNames(ptrSize)
	ts := []*typ{n["Bool"], n["Int8"], n["UInt8"], n["Int16"], n["UInt16"], n["Int32"], n["UInt32"]}
	if ptrSize == 8 {
		ts = append(ts, n["Int64"], n["UInt64"])
	}
	ts = append(ts, n["Uintptr"], n["Float32"], n["Float64"], n["BytePtr"],
		&typ{name: "unsafe.Pointer", kind: tUnsafePtr, size: ptrSize, align: ptrSize, ptrs: yes})
	if store {
		ts = append(ts, &typ{name: "struct{ p *T }", kind: tStruct, size: ptrSize, align: ptrSize, ptrs: yes})
	}
	return ts
}

func simdType(size int64) *typ {
	return &typ{name: fmt.Sprintf("%d-byte SIMD type", size), kind: tStruct, size: size, align: min(size, 8), simd: true, ptrs: no}
}

// ptrSizes are the pointer sizes of the arches (cmd/internal/sys/arch.go).
var ptrSizes = map[string]int64{
	"386": 4, "ARM": 4, "MIPS": 4,
	"AMD64": 8, "ARM64": 8, "LOONG64": 8, "MIPS64": 8, "PPC64": 8, "RISCV64": 8, "S390X": 8, "Wasm": 8,
}
