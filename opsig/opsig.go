// Package opsig describes the operand and result types of generic SSA ops:
// what kind of value each argument and the result is, its width in bits
// when the op fixes it, and its signedness when the op implies one.
//
// For example, Rsh32Ux64 takes a 32-bit value interpreted as unsigned and a
// 64-bit unsigned shift count, and produces a 32-bit value; Load takes a
// pointer and memory and produces a value whose kind and width come from
// its type.
package opsig

import "github.com/josharian/unruly/ops"

// Kind is the kind of an operand.
type Kind uint8

const (
	Unknown Kind = iota // not described (the operands of generated SIMD ops)
	Any                 // determined by the value's type (Load, Phi, Copy, CondSelect, ...)

	// Int is an integer, including uintptr.
	Int
	Float // floating point
	Bool

	// Ptr is a pointer-shaped value (a pointer, unsafe.Pointer, map, chan,
	// or func) or a uintptr that holds an address. SSA does not keep
	// these apart from pointer-sized integers: SB, ITab, and GetCallerPC
	// have type uintptr, and rules compare integer constants with EqPtr.
	// Analyzers should accept a pointer-sized Int where a Ptr is expected
	// and vice versa.
	Ptr

	Mem       // memory state
	Flags     // carry/borrow flags, as in Add32carry
	Void      // no value
	Tuple     // a two-element tuple; see Operand.Elems
	Results   // the results of a call, followed by memory (select with SelectN)
	String    // string header
	Slice     // slice header
	Interface // interface pair
	Complex   // complex number
	Struct    // struct value
	Array     // array value
	Vector    // SIMD vector or mask
)

// Sign is how an op interprets an integer operand.
type Sign uint8

const (
	SignAny  Sign = iota // signedness is irrelevant (e.g. Add32) or not applicable
	Signed               // interpreted as signed (e.g. Less32, Rsh32x64's arg0)
	Unsigned             // interpreted as unsigned (e.g. Less32U, shift counts)
)

// Operand describes one argument or result of an op.
type Operand struct {
	Kind Kind
	// Width is the width in bits, if fixed by the op (Add32: 32).
	// It is 0 if the width comes from the value's type
	// (Load, Ctz64's int result, pointers).
	Width int
	// Sign is how the op interprets the operand. For a result, it is the
	// interpretation under which the op defines its value (Div64u's
	// quotient is unsigned) and agrees with the op's default type, if any.
	// It does not constrain the signedness of the value's type, which SSA
	// does not track reliably: dec64 builds Rsh32x32 values of type UInt32.
	Sign  Sign
	Elems []Operand // for Tuple: the elements
}

// Sig is the signature of a generic op.
type Sig struct {
	Args   []Operand // one per argument; for a variadic op, see Variadic
	Result Operand
	// Variadic, if non-nil, describes every argument of a variadic op
	// (ArgLength -1); Args is then empty.
	Variadic *Operand
	// SIMD reports a machine-generated SIMD op (ops.Op.SIMD), whose
	// operands are not described: they have Kind Unknown.
	SIMD bool
}

// Lookup returns the signature of the generic op op.
// It reports false for non-generic ops and for ops it does not know,
// such as ops added to Go after this table was written, or ops whose
// arity differs from the table's.
func Lookup(op *ops.Op) (Sig, bool) {
	if !op.IsGeneric() {
		return Sig{}, false
	}
	if op.SIMD {
		s := Sig{SIMD: true}
		if op.ArgLength < 0 {
			s.Variadic = &Operand{}
		} else {
			s.Args = make([]Operand, op.ArgLength)
		}
		return s, true
	}
	s, ok := table[op.Name]
	if !ok || (s.Variadic != nil) != (op.ArgLength < 0) || (s.Variadic == nil && len(s.Args) != int(op.ArgLength)) {
		return Sig{}, false
	}
	return s, true
}
