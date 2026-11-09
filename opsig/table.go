package opsig

import "fmt"

// The table covers every generic op in genericOps.go except the
// machine-generated SIMD ops. Its sources are the op comments in
// genericOps.go, the values ssagen constructs, and the rules that use
// the ops. Widths and signedness are claimed only where those agree;
// elsewhere the table says less (Width 0, SignAny).

func integer(w int) Operand  { return Operand{Kind: Int, Width: w} }
func signed(w int) Operand   { return Operand{Kind: Int, Width: w, Sign: Signed} }
func unsigned(w int) Operand { return Operand{Kind: Int, Width: w, Sign: Unsigned} }
func float(w int) Operand    { return Operand{Kind: Float, Width: w} }

func tuple(a, b Operand) Operand { return Operand{Kind: Tuple, Elems: []Operand{a, b}} }

var (
	anyv      = Operand{Kind: Any}
	boolean   = Operand{Kind: Bool}
	ptr       = Operand{Kind: Ptr}
	mem       = Operand{Kind: Mem}
	flags     = Operand{Kind: Flags}
	void      = Operand{Kind: Void}
	results   = Operand{Kind: Results}
	str       = Operand{Kind: String}
	slice     = Operand{Kind: Slice}
	iface     = Operand{Kind: Interface}
	complexv  = Operand{Kind: Complex}
	structv   = Operand{Kind: Struct}
	array     = Operand{Kind: Array}
	vector    = Operand{Kind: Vector}
	intSized  = integer(0) // int- or pointer-sized integer; width from the type
	signedInt = signed(0)
)

func sig(result Operand, args ...Operand) Sig { return Sig{Result: result, Args: args} }

func variadic(result, each Operand) Sig { return Sig{Result: result, Variadic: &each} }

var table = buildTable()

func buildTable() map[string]Sig {
	t := make(map[string]Sig)
	add := func(name string, s Sig) {
		if _, dup := t[name]; dup {
			panic("opsig: duplicate op " + name)
		}
		t[name] = s
	}
	addf := func(s Sig, format string, args ...any) { add(fmt.Sprintf(format, args...), s) }

	widths := []int{8, 16, 32, 64}

	// Pseudo-op: (Last a b c) is c; dec64 uses it for let bindings.
	add("Last", variadic(anyv, anyv))

	for _, w := range widths {
		x := integer(w)
		for _, op := range []string{"Add", "Sub", "Mul", "And", "Or", "Xor"} {
			addf(sig(x, x, x), "%s%d", op, w)
		}
		addf(sig(x, x), "Neg%d", w)
		addf(sig(x, x), "Com%d", w)

		s, u := signed(w), unsigned(w)
		for _, op := range []string{"Div", "Mod"} {
			addf(sig(s, s, s), "%s%d", op, w)
			addf(sig(u, u, u), "%s%du", op, w)
		}

		addf(sig(boolean, x, x), "Eq%d", w)
		addf(sig(boolean, x, x), "Neq%d", w)
		for _, op := range []string{"Less", "Leq"} {
			addf(sig(boolean, s, s), "%s%d", op, w)
			addf(sig(boolean, u, u), "%s%dU", op, w)
		}

		// ssagen gives the counts type int (math/bits returns int);
		// rules give them other types, such as UInt32 in dec64.
		addf(sig(intSized, x), "Ctz%d", w)
		addf(sig(intSized, x), "Ctz%dNonZero", w)
		addf(sig(intSized, x), "BitLen%d", w)
		addf(sig(intSized, x), "PopCount%d", w)

		addf(sig(x, x), "BitRev%d", w)
		if w > 8 {
			// ssagen gives PPC64's Bswap16 (for bits.ReverseBytes16)
			// type uint rather than uint16; it still swaps 16 bits.
			addf(sig(x, x), "Bswap%d", w)
		}

		// Only the low log2(w) bits of the count matter, so its width
		// and signedness do not (genericOps.go).
		addf(sig(x, x, intSized), "RotateLeft%d", w)

		// Shift counts are unsigned (genericOps.go).
		for _, c := range widths {
			addf(sig(x, x, unsigned(c)), "Lsh%dx%d", w, c)
			addf(sig(s, s, unsigned(c)), "Rsh%dx%d", w, c)
			addf(sig(u, u, unsigned(c)), "Rsh%dUx%d", w, c)
		}

		for _, to := range widths {
			if to <= w {
				continue
			}
			addf(sig(signed(to), s), "SignExt%dto%d", w, to)
			addf(sig(unsigned(to), u), "ZeroExt%dto%d", w, to)
			addf(sig(x, integer(to)), "Trunc%dto%d", to, w)
		}
	}

	add("AddPtr", sig(ptr, ptr, intSized))
	// SubPtr is lowered on AMD64 but never constructed, and
	// genericOps.go does not say what its operands are.
	add("SubPtr", sig(anyv, anyv, anyv))

	add("Hmul32", sig(signed(32), signed(32), signed(32)))
	add("Hmul32u", sig(unsigned(32), unsigned(32), unsigned(32)))
	add("Hmul64", sig(signed(64), signed(64), signed(64)))
	add("Hmul64u", sig(unsigned(64), unsigned(64), unsigned(64)))

	// The high word, carry, borrow, or overflow these ops produce
	// depends on reading their inputs as unsigned.
	for _, w := range []int{32, 64} {
		u := unsigned(w)
		addf(sig(tuple(u, u), u, u), "Mul%duhilo", w)
		// ssagen's MulUintptr types the tuple (uint, uint), but its
		// second element is a bool: rules build it with ConstBool
		// and lower it to SETO and the like.
		addf(sig(tuple(u, boolean), u, u), "Mul%duover", w)
		addf(sig(u, u, u), "Avg%du", w)
	}
	add("Div128u", sig(tuple(unsigned(64), unsigned(64)), unsigned(64), unsigned(64), unsigned(64)))

	for _, w := range []int{32, 64} {
		x := float(w)
		for _, op := range []string{"Add", "Sub", "Mul", "Div", "Min", "Max"} {
			addf(sig(x, x, x), "%s%dF", op, w)
		}
		addf(sig(x, x, x), "Min%dFSel", w)
		addf(sig(x, x, x), "Max%dFSel", w)
		addf(sig(x, x), "Neg%dF", w)
		addf(sig(x, x), "Round%dF", w)
		for _, op := range []string{"Eq", "Neq", "Less", "Leq"} {
			addf(sig(boolean, x, x), "%s%dF", op, w)
		}
		for _, iw := range []int{32, 64} {
			addf(sig(x, signed(iw)), "Cvt%dto%dF", iw, w)
			addf(sig(signed(iw), x), "Cvt%dFto%d", w, iw)
			addf(sig(x, unsigned(iw)), "Cvt%dUto%dF", iw, w)
			addf(sig(unsigned(iw), x), "Cvt%dFto%dU", w, iw)
		}
	}
	add("Cvt32Fto64F", sig(float(64), float(32)))
	add("Cvt64Fto32F", sig(float(32), float(64)))
	add("CvtBoolToUint8", sig(integer(8), boolean)) // 0 or 1

	add("EqPtr", sig(boolean, ptr, ptr))
	add("NeqPtr", sig(boolean, ptr, ptr))
	add("EqInter", sig(boolean, iface, iface))
	add("NeqInter", sig(boolean, iface, iface))
	add("EqSlice", sig(boolean, slice, slice))
	add("NeqSlice", sig(boolean, slice, slice))

	// arg2 ? arg0 : arg1; check.go requires arg2 to be boolean.
	add("CondSelect", sig(anyv, anyv, anyv, boolean))

	add("AndB", sig(boolean, boolean, boolean))
	add("OrB", sig(boolean, boolean, boolean))
	add("EqB", sig(boolean, boolean, boolean))
	add("NeqB", sig(boolean, boolean, boolean))
	add("Not", sig(boolean, boolean))

	// Count trailing zeros of arg1<<32 | arg0; ssagen passes Int64Lo
	// and Int64Hi.
	add("Ctz64On32", sig(intSized, integer(32), integer(32)))

	// The float64-only math ops (genericOps.go; ssagen and the rules
	// use them only with float64).
	f64 := float(64)
	add("Sqrt", sig(f64, f64))
	add("Sqrt32", sig(float(32), float(32)))
	for _, op := range []string{"Floor", "Ceil", "Trunc", "Round", "RoundToEven", "Abs"} {
		add(op, sig(f64, f64))
	}
	add("Copysign", sig(f64, f64, f64))
	add("FMA", sig(f64, f64, f64, f64))
	add("FMA32", sig(float(32), float(32), float(32), float(32)))

	add("Min64", sig(signed(64), signed(64), signed(64)))
	add("Max64", sig(signed(64), signed(64), signed(64)))
	add("Min64u", sig(unsigned(64), unsigned(64), unsigned(64)))
	add("Max64u", sig(unsigned(64), unsigned(64), unsigned(64)))

	add("Phi", variadic(anyv, anyv))
	add("Copy", sig(anyv, anyv))
	// Converts between unsafe.Pointer and uintptr.
	add("Convert", sig(ptr, ptr, mem))

	add("ConstBool", sig(boolean))
	add("ConstString", sig(str))
	add("ConstNil", sig(ptr))
	for _, w := range widths {
		addf(sig(integer(w)), "Const%d", w)
	}
	add("Const32F", sig(float(32)))
	add("Const64F", sig(float(64)))
	add("ConstInterface", sig(iface))
	add("ConstSlice", sig(slice))

	add("InitMem", sig(mem))
	add("Arg", sig(anyv))
	add("ArgIntReg", sig(anyv)) // an integer or a pointer
	add("ArgFloatReg", sig(float(0)))

	add("Addr", sig(ptr, ptr))           // arg0 is SB
	add("LocalAddr", sig(ptr, ptr, mem)) // arg0 is SP
	add("SP", sig(ptr))
	add("SB", sig(ptr))
	add("Invalid", sig(anyv))
	add("SPanchored", sig(ptr, ptr, mem))

	add("Load", sig(anyv, ptr, mem))
	add("Dereference", sig(anyv, ptr, mem))
	add("Store", sig(mem, ptr, anyv, mem))
	add("Move", sig(mem, ptr, ptr, mem))
	add("Zero", sig(mem, ptr, mem))
	add("StoreWB", sig(mem, ptr, anyv, mem))
	add("MoveWB", sig(mem, ptr, ptr, mem))
	add("ZeroWB", sig(mem, ptr, mem))
	add("WBend", sig(mem, mem))
	add("WB", sig(tuple(ptr, mem), mem))

	add("HasCPUFeature", sig(boolean))

	// Bounds-check indexes and lengths are int-sized (ssagen's
	// extendIndex). PanicExtend, only on 32-bit archs, splits an int64
	// index into Int64Hi and Int64Lo.
	add("PanicBounds", sig(mem, intSized, intSized, mem))
	add("PanicExtend", sig(mem, integer(32), integer(32), intSized, mem))

	// Calls take a code pointer, context pointer, or nothing first,
	// then the inputs, then memory.
	for _, op := range []string{
		"ClosureCall", "StaticCall", "InterCall", "TailCall", "TailCallInter",
		"ClosureLECall", "StaticLECall", "InterLECall", "TailLECall", "TailLECallInter",
	} {
		add(op, variadic(results, anyv))
	}

	add("IsNonNil", sig(boolean, ptr))
	// 0 <= arg0 < arg1 (or <=) with arg1 >= 0 reads the same whether
	// arg0 is signed or unsigned.
	add("IsInBounds", sig(boolean, intSized, intSized))
	add("IsSliceInBounds", sig(boolean, intSized, intSized))
	add("SpectreIndex", sig(intSized, intSized, intSized))
	add("SpectreSliceIndex", sig(intSized, intSized, intSized))
	// The result is the pointer until scheduling, then Void (check.go);
	// generic NilChecks are lowered before then.
	add("NilCheck", sig(ptr, ptr, mem))

	add("GetG", sig(ptr, mem))
	add("GetClosurePtr", sig(ptr))
	add("GetCallerPC", sig(ptr))
	add("GetCallerSP", sig(ptr, mem))

	add("PtrIndex", sig(ptr, ptr, intSized))
	add("OffPtr", sig(ptr, ptr))

	add("SliceMake", sig(slice, ptr, intSized, intSized))
	add("SlicePtr", sig(ptr, slice))
	add("SliceLen", sig(signedInt, slice))
	add("SliceCap", sig(signedInt, slice))
	add("SlicePtrUnchecked", sig(ptr, slice))

	// Real and imaginary parts are float32 or float64.
	add("ComplexMake", sig(complexv, float(0), float(0)))
	add("ComplexReal", sig(float(0), complexv))
	add("ComplexImag", sig(float(0), complexv))

	add("StringMake", sig(str, ptr, intSized))
	add("StringPtr", sig(ptr, str))
	add("StringLen", sig(signedInt, str))

	// A direct interface's data word can be a one-pointer struct or
	// array: ssagen gives IData the asserted type, and dec.rules unwraps
	// IMake (StructMake ...).
	add("IMake", sig(iface, ptr, anyv))
	add("ITab", sig(ptr, iface))
	add("IData", sig(anyv, iface))

	// dec.rules applies StructSelect and ArraySelect to pointer-shaped
	// values that stand for one-pointer structs and arrays.
	add("StructMake", variadic(structv, anyv))
	add("StructSelect", sig(anyv, anyv))
	add("ArrayMake1", sig(array, anyv))
	add("ArraySelect", sig(anyv, anyv))

	add("StoreReg", sig(anyv, anyv))
	add("LoadReg", sig(anyv, anyv))
	add("FwdRef", sig(anyv))
	add("Unknown", sig(anyv))

	add("VarDef", sig(mem, mem))
	add("VarLive", sig(mem, mem))
	add("KeepAlive", sig(mem, anyv, mem))
	add("InlMark", sig(void, mem))

	// Ops for 64-bit integers on 32-bit archs.
	add("Int64Make", sig(unsigned(64), integer(32), integer(32))) // hi, lo
	add("Int64Hi", sig(unsigned(32), integer(64)))
	add("Int64Lo", sig(unsigned(32), integer(64)))
	u32 := unsigned(32)
	add("Add32carry", sig(tuple(u32, flags), u32, u32))
	add("Add32carrywithcarry", sig(tuple(u32, flags), u32, u32, flags))
	add("Add32withcarry", sig(integer(32), integer(32), integer(32), flags))
	add("Sub32carry", sig(tuple(u32, flags), u32, u32))
	add("Sub32withcarry", sig(integer(32), integer(32), integer(32), flags))
	u64 := unsigned(64)
	add("Add64carry", sig(tuple(u64, u64), u64, u64, u64)) // arg2 is 0 or 1
	add("Sub64borrow", sig(tuple(u64, u64), u64, u64, u64))
	// Signmask and Zeromask exist only on 32-bit archs (386, ARM, MIPS).
	add("Signmask", sig(signed(32), signed(32)))
	add("Zeromask", sig(unsigned(32), integer(32)))
	// 0 if arg0 == 0, -1 if arg0 > 0, undefined if arg0 < 0.
	add("Slicemask", sig(intSized, signedInt))

	add("Select0", sig(anyv, Operand{Kind: Tuple}))
	add("Select1", sig(anyv, Operand{Kind: Tuple}))
	add("MakeTuple", sig(tuple(anyv, anyv), anyv, anyv))
	add("SelectN", sig(anyv, results))
	add("SelectNAddr", sig(ptr, results))
	add("MakeResult", variadic(results, anyv))

	for _, w := range []int{8, 32, 64} {
		x, u := integer(w), unsigned(w)
		addf(sig(tuple(u, mem), ptr, mem), "AtomicLoad%d", w)
		addf(sig(mem, ptr, x, mem), "AtomicStore%d", w)
		addf(sig(mem, ptr, x, mem), "AtomicStore%dVariant", w)
		addf(sig(tuple(u, mem), ptr, x, mem), "AtomicExchange%d", w)
		addf(sig(tuple(u, mem), ptr, x, mem), "AtomicExchange%dVariant", w)
		for _, op := range []string{"And", "Or"} {
			addf(sig(tuple(u, mem), ptr, x, mem), "Atomic%s%dvalue", op, w)
			addf(sig(tuple(u, mem), ptr, x, mem), "Atomic%s%dvalueVariant", op, w)
		}
	}
	for _, w := range []int{32, 64} {
		x, u := integer(w), unsigned(w)
		addf(sig(tuple(u, mem), ptr, mem), "AtomicLoadAcq%d", w)
		addf(sig(mem, ptr, x, mem), "AtomicStoreRel%d", w)
		addf(sig(tuple(u, mem), ptr, x, mem), "AtomicAdd%d", w)
		addf(sig(tuple(u, mem), ptr, x, mem), "AtomicAdd%dVariant", w)
		addf(sig(tuple(boolean, mem), ptr, x, x, mem), "AtomicCompareAndSwap%d", w)
		addf(sig(tuple(boolean, mem), ptr, x, x, mem), "AtomicCompareAndSwap%dVariant", w)
	}
	add("AtomicLoadPtr", sig(tuple(ptr, mem), ptr, mem))
	add("AtomicStorePtrNoWB", sig(mem, ptr, ptr, mem))
	add("AtomicCompareAndSwapRel32", sig(tuple(boolean, mem), ptr, integer(32), integer(32), mem))
	for _, w := range []int{8, 32} {
		addf(sig(mem, ptr, integer(w), mem), "AtomicAnd%d", w)
		addf(sig(mem, ptr, integer(w), mem), "AtomicOr%d", w)
	}

	add("PubBarrier", sig(mem, mem))
	add("Clobber", sig(void))
	add("ClobberReg", sig(void))
	// The address is a uintptr (internal/runtime/sys.Prefetch).
	add("PrefetchCache", sig(mem, ptr, mem))
	add("PrefetchCacheStreamed", sig(mem, ptr, mem))
	add("MemEq", sig(boolean, ptr, ptr, intSized, mem)) // size is a uintptr
	add("Empty", sig(anyv))

	add("I32AsF32", sig(float(32), integer(32)))
	add("F32AsI32", sig(signed(32), float(32)))
	add("I64AsF64", sig(float(64), integer(64)))
	add("F64AsI64", sig(signed(64), float(64)))

	// Hand-written SIMD ops.
	add("ZeroSIMD", sig(vector))
	// Mask<elem>x<lanes>FromBits and ToBits take and return an unsigned
	// integer of the width in the op's name.
	for _, m := range []struct{ elem, lanes, bits int }{
		{8, 16, 16}, {8, 32, 32}, {8, 64, 64},
		{16, 8, 8}, {16, 16, 16}, {16, 32, 32},
		{32, 4, 8}, {32, 8, 8}, {32, 16, 16},
		{64, 2, 8}, {64, 4, 8}, {64, 8, 8},
	} {
		addf(sig(vector, integer(m.bits)), "Cvt%dtoMask%dx%d", m.bits, m.elem, m.lanes)
		addf(sig(integer(m.bits), vector), "CvtMask%dx%dto%d", m.elem, m.lanes, m.bits)
	}
	add("IsZeroVec", sig(boolean, vector))
	for _, v := range []string{"32x4", "32x8", "32x16", "64x2", "64x4", "64x8"} {
		add("IsNaNFloat"+v, sig(vector, vector))
	}
	add("ScalableVectorLen", sig(intSized)) // in bytes; ssagen types it int
	// Counts are ints, compared signed by ARM64's PWHILELT lowering.
	add("Count8s", sig(vector, signedInt))
	for _, e := range []struct {
		name string
		elem Operand
	}{
		{"Int8", integer(8)}, {"Uint8", integer(8)},
		{"Int16", integer(16)}, {"Uint16", integer(16)},
		{"Int32", integer(32)}, {"Uint32", integer(32)}, {"Float32", float(32)},
		{"Int64", integer(64)}, {"Uint64", integer(64)}, {"Float64", float(64)},
	} {
		add("IfElse"+e.name+"s", sig(vector, vector, vector, vector)) // x, mask, y
		add("Broadcast"+e.name+"s", sig(vector, e.elem))
	}
	// amd64 Masked (x, mask) and IfElse (x, mask, y), named by element width.
	for _, e := range []string{"8", "16", "32", "64", "Float32", "Float64"} {
		add("Masked"+e, sig(vector, vector, vector))
		add("IfElse"+e, sig(vector, vector, vector, vector))
	}
	for _, w := range widths {
		addf(sig(vector), "Mask%dsAllTrue", w)
		addf(sig(vector, signedInt), "Mask%dsFromCount", w)
		addf(sig(vector, vector), "Mask%dsFirst", w)
		addf(sig(vector, vector), "Mask%dsNext", w)
		addf(sig(boolean, vector), "Mask%dsAll", w)
		addf(sig(boolean, vector), "Mask%dsNone", w)
		addf(sig(boolean, vector), "Mask%dsAny", w)
		// The number is the element width; the mask is a vector (or an
		// ARM64 SVE predicate) and the value is a vector of any element type.
		addf(sig(vector, ptr, vector, mem), "LoadMasked%d", w)
		addf(sig(mem, ptr, vector, vector, mem), "StoreMasked%d", w)
	}

	return t
}
