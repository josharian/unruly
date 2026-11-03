package gensem

import (
	"fmt"
	"math"
	"strings"
)

// Kind is the kind of a Val.
type Kind uint8

const (
	KInvalid Kind = iota
	KInt          // an integer of Width bits; signedness is up to the op
	KFloat        // a float32 (Width 32) or float64 (Width 64), as IEEE bits
	KBool
	KFlags // a carry flag: Bits is 0 or 1
	KTuple
	// KPtr is a pointer: Bits bytes past the start of object Base, or
	// the address Bits if Base is 0. Distinct objects never overlap.
	KPtr
	KMem // a memory state
)

// Val is the run-time value of an SSA value.
type Val struct {
	Kind  Kind
	Width int    // in bits, for KInt and KFloat
	Bits  uint64 // zero above Width
	Elems []Val  // for KTuple
	Base  int    // for KPtr
}

// PtrVal returns a pointer of width w, off bytes into object base.
func PtrVal(w, base int, off uint64) Val {
	return Val{Kind: KPtr, Width: w, Base: base, Bits: off & mask(w)}
}

func mask(w int) uint64 {
	if w >= 64 {
		return ^uint64(0)
	}
	return 1<<uint(w) - 1
}

// sext sign-extends the low w bits of x.
func sext(x uint64, w int) int64 {
	s := 64 - uint(w)
	return int64(x<<s) >> s
}

// IntVal returns the w-bit integer with the low w bits of x.
func IntVal(w int, x uint64) Val { return Val{Kind: KInt, Width: w, Bits: x & mask(w)} }

// BoolVal returns b as a Val.
func BoolVal(b bool) Val {
	if b {
		return Val{Kind: KBool, Bits: 1}
	}
	return Val{Kind: KBool}
}

// FloatVal returns f rounded to width w (32 or 64).
func FloatVal(w int, f float64) Val {
	if w == 32 {
		return Val{Kind: KFloat, Width: 32, Bits: uint64(math.Float32bits(float32(f)))}
	}
	return Val{Kind: KFloat, Width: 64, Bits: math.Float64bits(f)}
}

// Float32Val returns f as a Val.
func Float32Val(f float32) Val {
	return Val{Kind: KFloat, Width: 32, Bits: uint64(math.Float32bits(f))}
}

// TupleVal returns the tuple (a, b).
func TupleVal(a, b Val) Val { return Val{Kind: KTuple, Elems: []Val{a, b}} }

// Int returns x's bits sign-extended from its width.
func (x Val) Int() int64 { return sext(x.Bits, x.Width) }

// Bool reports whether a KBool is true.
func (x Val) Bool() bool { return x.Bits != 0 }

// Float returns a KFloat's value.
func (x Val) Float() float64 {
	if x.Width == 32 {
		return float64(math.Float32frombits(uint32(x.Bits)))
	}
	return math.Float64frombits(x.Bits)
}

// Equal reports whether x and y are the same value. Any two NaNs of the
// same width are equal: the compiler does not preserve NaN payloads.
func (x Val) Equal(y Val) bool {
	if x.Kind != y.Kind || x.Width != y.Width || x.Base != y.Base {
		return false
	}
	switch x.Kind {
	case KFloat:
		if math.IsNaN(x.Float()) && math.IsNaN(y.Float()) {
			return true
		}
	case KTuple:
		if len(x.Elems) != len(y.Elems) {
			return false
		}
		for i := range x.Elems {
			if !x.Elems[i].Equal(y.Elems[i]) {
				return false
			}
		}
		return true
	}
	return x.Bits == y.Bits
}

func (x Val) String() string {
	switch x.Kind {
	case KInt:
		s := x.Int()
		if s >= -16 && s <= 16 {
			return fmt.Sprint(s)
		}
		return fmt.Sprintf("%d (%#x)", s, x.Bits)
	case KFloat:
		f := x.Float()
		if f == 0 && math.Signbit(f) {
			return "-0.0"
		}
		return fmt.Sprintf("%v", f)
	case KBool:
		return fmt.Sprint(x.Bool())
	case KFlags:
		return fmt.Sprintf("carry=%d", x.Bits)
	case KPtr:
		switch {
		case x.Base == 0 && x.Bits == 0:
			return "nil"
		case x.Base == 0:
			return fmt.Sprintf("%#x", x.Bits)
		case x.Bits == 0:
			return fmt.Sprintf("&obj%d", x.Base)
		}
		return fmt.Sprintf("&obj%d+%d", x.Base, x.Int())
	case KMem:
		return "mem"
	case KTuple:
		var s []string
		for _, e := range x.Elems {
			s = append(s, e.String())
		}
		return "(" + strings.Join(s, ", ") + ")"
	}
	return "invalid"
}
