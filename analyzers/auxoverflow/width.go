package auxoverflow

import (
	"regexp"
	"strings"

	"github.com/josharian/unruly/ops"
)

// addrBits returns the number of address bits that a memory op's offset
// is added into. It is the pointer size (cmd/internal/sys's PtrSize),
// except on Wasm: pointers are 64 bits there, but memory ops use only
// the low 32 bits of the address (wasm/ssa.go loads and stores their
// address operand with getValue32), so offsets need only be right
// modulo 2^32.
func addrBits(a *ops.Arch) uint {
	switch a.Name {
	case "386", "ARM", "MIPS", "Wasm":
		return 32
	}
	return 64
}

// x86Scalar matches the mnemonics of x86 scalar integer instructions,
// whose operand size is their last letter (cmd/internal/obj/x86).
// Vector instructions (V...) take 8-bit selectors, not operands.
var x86Scalar = regexp.MustCompile(`^[A-UW-Z][A-Z0-9]*[BWLQ]$`)

// opBits returns the width in bits of the operation that op applies to
// its auxint immediate, or 0 if it is not known: the width of op's
// default integer type, else what op's mnemonic says.
func opBits(a *ops.Arch, op *ops.Op) uint {
	typ, _, _ := strings.Cut(strings.Trim(op.Typ, "()"), ",")
	switch typ {
	case "Int64", "UInt64":
		return 64
	case "Int32", "UInt32":
		return 32
	case "Int16", "UInt16":
		return 16
	case "Int8", "UInt8":
		return 8
	}
	asm := op.Asm
	switch a.Name {
	case "386", "AMD64":
		if !x86Scalar.MatchString(asm) {
			return 0
		}
		return map[byte]uint{'B': 8, 'W': 16, 'L': 32, 'Q': 64}[asm[len(asm)-1]]
	case "S390X":
		// s390x stores name their size (MOVB, MOVH, MOVW, MOVD);
		// other 32-bit instructions have a W (ADDW, CMPWU).
		switch asm {
		case "MOVB":
			return 8
		case "MOVH":
			return 16
		case "MOVW":
			return 32
		case "MOVD":
			return 64
		case "ADD", "SUB", "MULLD", "CMP", "CMPU", "ADDC":
			return 64
		}
		if strings.Contains(asm, "W") {
			return 32
		}
	default:
		// CMPW, TSTW, CMPWU, ...
		if strings.HasSuffix(asm, "W") || strings.HasSuffix(asm, "WU") {
			return 32
		}
	}
	return 0
}

// valIsSize reports whether the value half of op's SymValAndOff auxint
// is a count rather than an operand: it is not a scalar instruction
// whose operand width opBits knows, nor an x86 vector instruction,
// whose value is an 8-bit selector. Examples are S390X CLEAR and MVC,
// whose value is the number of bytes.
func valIsSize(a *ops.Arch, op *ops.Op) bool {
	if opBits(a, op) != 0 {
		return false
	}
	if (a.Name == "AMD64" || a.Name == "386") && op.Asm != "" {
		return false
	}
	return true
}

// mips64Imm are the MIPS64 ops with an int64 auxint that
// mips64/ssa.go emits as an immediate operand (p.From.Type =
// obj.TYPE_CONST; p.From.Offset = v.AuxInt). The MIPS assembler
// classifies a constant that does not fit in 32 bits as C_LCON anyway
// (obj/mips asm0.go aclass: "return C_LCON // C_DCON") and so silently
// truncates it. The shifts (SLLVconst, ...) are omitted: their count
// must be less than 64 anyway. MOVVconst is not among them: obj/mips obj0.go moves
// wider MOVV constants to memory.
var mips64Imm = map[string]bool{
	"ADDVconst":               true,
	"SUBVconst":               true,
	"ANDconst":                true,
	"ORconst":                 true,
	"XORconst":                true,
	"SGTconst":                true,
	"SGTUconst":               true,
	"LoweredAtomicAddconst64": true,
}

// zeroExtImm are the ops whose 32-bit immediate codegen zero-extends,
// so that int32(c) for c in [0, 1<<32) is right: s390x/ssa.go emits
// int64(uint32(v.AuxInt)) for CMPUconst (and CMPWUconst, a 32-bit
// operation). Whether such immediates are extended as rules expect is
// a question of signedness, not overflow.
var zeroExtImm = map[string]bool{
	"S390X.CMPUconst": true,
}
