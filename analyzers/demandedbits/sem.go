package demandedbits

// This file describes how many low bits of each argument some arch ops
// depend on. An op absent from these tables is not modeled: it imposes
// no demand on its arguments and passes none through, so it never causes
// a report. Every entry must be exact, because a demand that is too low
// in a match, or too high in a result, causes false reports.
//
// The widths come from the instruction each op assembles to (the op's
// asm in <arch>Ops.go, which <arch>/ssa.go emits via v.Op.Asm()) and the
// ISA's definition of that instruction:
//
//   - x86 (Intel SDM vol. 2): an instruction with a B/W/L/Q suffix reads
//     8/16/32/64 bits of its operands; shift counts are masked to 5 bits,
//     or 6 for 64-bit operands (SHL/SHR/SAR, SHLX/SHRX/SARX).
//   - ARM (ARM ARM A8.4.1): register-specified shifts use the bottom byte
//     of the shift register (ARMOps.go: "shift amount is mod 256").
//   - ARM64: ops without a W suffix are 64-bit; LSLV/LSRV/ASRV use the
//     shift register mod 64 (ARM64Ops.go).
//   - MIPS, MIPS64, LOONG64, RISCV64, PPC64, S390X: the shift-count
//     masks are those documented in each <arch>Ops.go and match the
//     ISA (e.g. PPC64 SLD uses 7 bits, SLW 6; LOONG64 SLL.W 5, SLL.D 6;
//     RISCV64 SLLW 5; S390X SLL and SLLG both 6).
//   - Wasm: i64.shl and friends take the count mod 64.

type argKind uint8

const (
	argNone  argKind = iota // not modeled: no known demand
	argFixed                // depends on the low w bits, whatever the demand
	argLow                  // the low d bits of the result depend on the low min(d, w) bits
	argExt                  // an extension of the low w bits
	argShl                  // the shifted value of a left shift by the auxint
	argShr                  // the shifted value of a right shift by the auxint
)

type argSem struct {
	kind argKind
	w    int
}

type opKind uint8

const (
	kindPlain     opKind = iota
	kindCtz              // count trailing zeros of arg0 (width args[0].w)
	kindClz              // count leading zeros of arg0
	kindRev              // reverse the bits of arg0 (modeled only under a CLZ)
	kindOr               // arg0 | arg1
	kindOrAux            // arg0 | auxint
	kindBitSetAux        // arg0 | 1<<auxint
	kindAnd              // arg0 & arg1
	kindAndAux           // arg0 & auxint
	kindConst            // the constant auxint
)

type opSem struct {
	kind opKind
	args []argSem
	// immBits, if nonzero, bounds a kindAndAux op's auxint to
	// [0, 1<<immBits) even when it is not a constant.
	immBits int
}

var none = argSem{kind: argNone}

func fixed(w int) argSem { return argSem{argFixed, w} }
func low(w int) argSem   { return argSem{argLow, w} }

func sem(kind opKind, args ...argSem) *opSem { return &opSem{kind: kind, args: args} }

// cmp is a compare of two w-bit registers; cmpc compares one with a constant.
func cmp(w int) *opSem  { return sem(kindPlain, fixed(w), fixed(w)) }
func cmpc(w int) *opSem { return sem(kindPlain, fixed(w)) }

// ext extends the low w bits of its argument.
func ext(w int) *opSem { return sem(kindPlain, argSem{argExt, w}) }

// lo2 and lo1 are w-bit ops whose low result bits depend only on the low
// bits of their (two or one) arguments, such as ADD and NEG.
func lo2(w int) *opSem { return sem(kindPlain, low(w), low(w)) }
func lo1(w int) *opSem { return sem(kindPlain, low(w)) }

// Shifts of a w-bit value by a register count that the hardware masks
// to amt bits, and by an auxint (shlc, shrc). The low d bits of x<<k
// depend on the low d-k bits of x; those of x>>k on the low d+k.
func shl(w, amt int) *opSem { return sem(kindPlain, argSem{argShl, w}, fixed(amt)) }
func shr(w, amt int) *opSem { return sem(kindPlain, argSem{argShr, w}, fixed(amt)) }
func shlc(w int) *opSem     { return sem(kindPlain, argSem{argShl, w}) }
func shrc(w int) *opSem     { return sem(kindPlain, argSem{argShr, w}) }

func ctz(w int) *opSem { return sem(kindCtz, fixed(w)) }
func clz(w int) *opSem { return sem(kindClz, fixed(w)) }
func rev(w int) *opSem { return sem(kindRev, argSem{argNone, w}) }

func or2(w int) *opSem  { return sem(kindOr, low(w), low(w)) }
func orc(w int) *opSem  { return sem(kindOrAux, low(w)) }
func and2(w int) *opSem { return sem(kindAnd, low(w), low(w)) }
func andc(w int) *opSem { return sem(kindAndAux, low(w)) }

// andc16 is andc whose auxint is always in [0, 0xFFFF].
func andc16(w int) *opSem { return &opSem{kind: kindAndAux, args: []argSem{low(w)}, immBits: 16} }

var konst = sem(kindConst)

// cas32 is a 32-bit compare-and-swap (ptr old new mem) that compares the
// sign-extended loaded word with all 64 bits of old.
var cas32 = sem(kindPlain, none, fixed(64), none, none)

var archTables = map[string]map[string]*opSem{
	"386": {
		"CMPL": cmp(32), "CMPW": cmp(16), "CMPB": cmp(8),
		"CMPLconst": cmpc(32), "CMPWconst": cmpc(16), "CMPBconst": cmpc(8),
		"TESTL": cmp(32), "TESTW": cmp(16), "TESTB": cmp(8),
		"TESTLconst": cmpc(32), "TESTWconst": cmpc(16), "TESTBconst": cmpc(8),
		"MOVBLSX": ext(8), "MOVBLZX": ext(8), "MOVWLSX": ext(16), "MOVWLZX": ext(16),
		"BSFL": ctz(32), "BSFW": ctz(16), "BSRL": clz(32), "BSRW": clz(16),
		"SHLL": shl(32, 5), "SHRL": shr(32, 5), "SHRW": shr(16, 5), "SHRB": shr(8, 5),
		"SARL": shr(32, 5), "SARW": shr(16, 5), "SARB": shr(8, 5),
		"SHLLconst": shlc(32), "SHRLconst": shrc(32), "SHRWconst": shrc(16), "SHRBconst": shrc(8),
		"SARLconst": shrc(32), "SARWconst": shrc(16), "SARBconst": shrc(8),
		"ADDL": lo2(32), "ADDLconst": lo1(32), "SUBL": lo2(32), "SUBLconst": lo1(32),
		"XORL": lo2(32), "XORLconst": lo1(32), "NEGL": lo1(32), "NOTL": lo1(32),
		"ORL": or2(32), "ORLconst": orc(32), "ANDL": and2(32), "ANDLconst": andc(32),
		"MOVLconst": konst,
	},
	"AMD64": {
		"CMPQ": cmp(64), "CMPL": cmp(32), "CMPW": cmp(16), "CMPB": cmp(8),
		"CMPQconst": cmpc(64), "CMPLconst": cmpc(32), "CMPWconst": cmpc(16), "CMPBconst": cmpc(8),
		"TESTQ": cmp(64), "TESTL": cmp(32), "TESTW": cmp(16), "TESTB": cmp(8),
		"TESTQconst": cmpc(64), "TESTLconst": cmpc(32), "TESTWconst": cmpc(16), "TESTBconst": cmpc(8),
		"MOVBQSX": ext(8), "MOVBQZX": ext(8), "MOVWQSX": ext(16), "MOVWQZX": ext(16),
		"MOVLQSX": ext(32), "MOVLQZX": ext(32),
		"BSFQ": ctz(64), "BSFL": ctz(32), "TZCNTQ": ctz(64), "TZCNTL": ctz(32),
		"BSRQ": clz(64), "BSRL": clz(32), "LZCNTQ": clz(64), "LZCNTL": clz(32),
		"SHLQ": shl(64, 6), "SHLL": shl(32, 5),
		"SHRQ": shr(64, 6), "SHRL": shr(32, 5), "SHRW": shr(16, 5), "SHRB": shr(8, 5),
		"SARQ": shr(64, 6), "SARL": shr(32, 5), "SARW": shr(16, 5), "SARB": shr(8, 5),
		"SHLXQ": shl(64, 6), "SHLXL": shl(32, 5),
		"SHRXQ": shr(64, 6), "SHRXL": shr(32, 5), "SARXQ": shr(64, 6), "SARXL": shr(32, 5),
		"SHLQconst": shlc(64), "SHLLconst": shlc(32),
		"SHRQconst": shrc(64), "SHRLconst": shrc(32), "SHRWconst": shrc(16), "SHRBconst": shrc(8),
		"SARQconst": shrc(64), "SARLconst": shrc(32), "SARWconst": shrc(16), "SARBconst": shrc(8),
		"ADDQ": lo2(64), "ADDL": lo2(32), "ADDQconst": lo1(64), "ADDLconst": lo1(32),
		"SUBQ": lo2(64), "SUBL": lo2(32), "SUBQconst": lo1(64), "SUBLconst": lo1(32),
		"XORQ": lo2(64), "XORL": lo2(32), "XORQconst": lo1(64), "XORLconst": lo1(32),
		"NEGQ": lo1(64), "NEGL": lo1(32), "NOTQ": lo1(64), "NOTL": lo1(32),
		"ORQ": or2(64), "ORL": or2(32), "ORQconst": orc(64), "ORLconst": orc(32),
		"BTSQconst": sem(kindBitSetAux, low(64)),
		"ANDQ":      and2(64), "ANDL": and2(32), "ANDQconst": andc(64), "ANDLconst": andc(32),
		"MOVQconst": konst, "MOVLconst": konst,
	},
	"ARM": {
		"CMP": cmp(32), "CMN": cmp(32), "TST": cmp(32),
		"CMPconst": cmpc(32), "CMNconst": cmpc(32), "TSTconst": cmpc(32),
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"CLZ": clz(32), "RBIT": rev(32),
		"SLL": shl(32, 8), "SRL": shr(32, 8), "SRA": shr(32, 8),
		"SLLconst": shlc(32), "SRLconst": shrc(32), "SRAconst": shrc(32),
		"ADD": lo2(32), "ADDconst": lo1(32), "SUB": lo2(32), "SUBconst": lo1(32),
		"XOR": lo2(32), "XORconst": lo1(32),
		"OR": or2(32), "ORconst": orc(32), "AND": and2(32), "ANDconst": andc(32),
		"MOVWconst": konst,
	},
	"ARM64": {
		"CMP": cmp(64), "CMN": cmp(64), "TST": cmp(64),
		"CMPW": cmp(32), "CMNW": cmp(32), "TSTW": cmp(32),
		"CMPconst": cmpc(64), "CMNconst": cmpc(64), "TSTconst": cmpc(64),
		"CMPWconst": cmpc(32), "CMNWconst": cmpc(32), "TSTWconst": cmpc(32),
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"MOVWreg": ext(32), "MOVWUreg": ext(32),
		"CLZ": clz(64), "CLZW": clz(32), "RBIT": rev(64), "RBITW": rev(32),
		"SLL": shl(64, 6), "SRL": shr(64, 6), "SRA": shr(64, 6),
		"SLLconst": shlc(64), "SRLconst": shrc(64), "SRAconst": shrc(64),
		"ADD": lo2(64), "ADDconst": lo1(64), "SUB": lo2(64), "SUBconst": lo1(64),
		"XOR": lo2(64), "XORconst": lo1(64), "NEG": lo1(64),
		"OR": or2(64), "ORconst": orc(64), "AND": and2(64), "ANDconst": andc(64),
		"MOVDconst": konst,
	},
	"LOONG64": {
		// SGT and SGTU compare full registers.
		"SGT": cmp(64), "SGTU": cmp(64), "SGTconst": cmpc(64), "SGTUconst": cmpc(64),
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"MOVWreg": ext(32), "MOVWUreg": ext(32),
		"CLZW": clz(32), "CLZV": clz(64), "CTZW": ctz(32), "CTZV": ctz(64),
		"BITREVW": rev(32), "BITREVV": rev(64),
		"SLL": shl(32, 5), "SRL": shr(32, 5), "SRA": shr(32, 5),
		"SLLV": shl(64, 6), "SRLV": shr(64, 6), "SRAV": shr(64, 6),
		"SLLconst": shlc(32), "SRLconst": shrc(32), "SRAconst": shrc(32),
		"SLLVconst": shlc(64), "SRLVconst": shrc(64), "SRAVconst": shrc(64),
		"ADDV": lo2(64), "ADDVconst": lo1(64), "SUBV": lo2(64), "SUBVconst": lo1(64),
		"XOR": lo2(64), "XORconst": lo1(64), "NEGV": lo1(64),
		"OR": or2(64), "ORconst": orc(64), "AND": and2(64), "ANDconst": andc(64),
		"MOVVconst": konst,
		// LL.W sign-extends the loaded word, which is compared with
		// the full 64 bits of the old value (loong64/ssa.go).
		"LoweredAtomicCas32":        cas32,
		"LoweredAtomicCas32Variant": cas32,
	},
	"MIPS": {
		"SGT": cmp(32), "SGTU": cmp(32), "SGTconst": cmpc(32), "SGTUconst": cmpc(32),
		"SGTzero": cmpc(32), "SGTUzero": cmpc(32),
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"CLZ": clz(32),
		"SLL": shl(32, 5), "SRL": shr(32, 5), "SRA": shr(32, 5),
		"SLLconst": shlc(32), "SRLconst": shrc(32), "SRAconst": shrc(32),
		"ADD": lo2(32), "ADDconst": lo1(32), "SUB": lo2(32), "SUBconst": lo1(32),
		"XOR": lo2(32), "XORconst": lo1(32), "NEG": lo1(32),
		"OR": or2(32), "ORconst": orc(32), "AND": and2(32), "ANDconst": andc(32),
		"MOVWconst": konst,
	},
	"MIPS64": {
		"SGT": cmp(64), "SGTU": cmp(64), "SGTconst": cmpc(64), "SGTUconst": cmpc(64),
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"MOVWreg": ext(32), "MOVWUreg": ext(32),
		"SLLV": shl(64, 6), "SRLV": shr(64, 6), "SRAV": shr(64, 6),
		"SLLVconst": shlc(64), "SRLVconst": shrc(64), "SRAVconst": shrc(64),
		"ADDV": lo2(64), "ADDVconst": lo1(64), "SUBV": lo2(64), "SUBVconst": lo1(64),
		"XOR": lo2(64), "XORconst": lo1(64), "NEGV": lo1(64),
		"OR": or2(64), "ORconst": orc(64), "AND": and2(64), "ANDconst": andc(64),
		"MOVVconst": konst,
		// LL sign-extends the loaded word, which is compared with
		// the full 64 bits of the old value (mips64/ssa.go).
		"LoweredAtomicCas32": cas32,
	},
	"PPC64": {
		"CMP": cmp(64), "CMPU": cmp(64), "CMPW": cmp(32), "CMPWU": cmp(32),
		"CMPconst": cmpc(64), "CMPUconst": cmpc(64), "CMPWconst": cmpc(32), "CMPWUconst": cmpc(32),
		"MOVBreg": ext(8), "MOVBZreg": ext(8), "MOVHreg": ext(16), "MOVHZreg": ext(16),
		"MOVWreg": ext(32), "MOVWZreg": ext(32),
		"CNTLZW": clz(32), "CNTLZD": clz(64), "CNTTZW": ctz(32), "CNTTZD": ctz(64),
		"SLD": shl(64, 7), "SRD": shr(64, 7), "SRAD": shr(64, 7),
		"SLW": shl(32, 6), "SRW": shr(32, 6), "SRAW": shr(32, 6),
		"SLDconst": shlc(64), "SRDconst": shrc(64), "SRADconst": shrc(64),
		"SLWconst": shlc(32), "SRWconst": shrc(32), "SRAWconst": shrc(32),
		"ADD": lo2(64), "ADDconst": lo1(64), "SUB": lo2(64),
		"XOR": lo2(64), "XORconst": lo1(64), "NEG": lo1(64),
		"OR": or2(64), "ORconst": orc(64), "AND": and2(64),
		// ANDconst assembles to andi., whose immediate is an unsigned
		// 16-bit value, and every rule that builds ANDconst guarantees
		// that (isU16Bit, uint8, uint16, or a mask of an existing one).
		"ANDconst":  andc16(64),
		"MOVDconst": konst,
	},
	"RISCV64": {
		"MOVBreg": ext(8), "MOVBUreg": ext(8), "MOVHreg": ext(16), "MOVHUreg": ext(16),
		"MOVWreg": ext(32), "MOVWUreg": ext(32),
		"CLZ": clz(64), "CLZW": clz(32), "CTZ": ctz(64), "CTZW": ctz(32),
		"SLL": shl(64, 6), "SRL": shr(64, 6), "SRA": shr(64, 6),
		"SLLW": shl(32, 5), "SRLW": shr(32, 5), "SRAW": shr(32, 5),
		"SLLI": shlc(64), "SRLI": shrc(64), "SRAI": shrc(64),
		"SLLIW": shlc(32), "SRLIW": shrc(32), "SRAIW": shrc(32),
		"ADD": lo2(64), "ADDI": lo1(64), "ADDIW": lo1(32), "SUB": lo2(64), "SUBW": lo2(32),
		"XOR": lo2(64), "XORI": lo1(64), "NEG": lo1(64), "NEGW": lo1(32), "NOT": lo1(64),
		"OR": or2(64), "ORI": orc(64), "AND": and2(64), "ANDI": andc(64),
		"MOVDconst": konst,
		// LR.W sign-extends the loaded word, which is compared with
		// the full 64 bits of the old value (riscv64/ssa.go).
		"LoweredAtomicCas32": cas32,
	},
	"S390X": {
		"CMP": cmp(64), "CMPU": cmp(64), "CMPW": cmp(32), "CMPWU": cmp(32),
		"CMPconst": cmpc(64), "CMPUconst": cmpc(64), "CMPWconst": cmpc(32), "CMPWUconst": cmpc(32),
		"MOVBreg": ext(8), "MOVBZreg": ext(8), "MOVHreg": ext(16), "MOVHZreg": ext(16),
		"MOVWreg": ext(32), "MOVWZreg": ext(32),
		"FLOGR": clz(64),
		"SLD":   shl(64, 6), "SRD": shr(64, 6), "SRAD": shr(64, 6),
		"SLW": shl(32, 6), "SRW": shr(32, 6), "SRAW": shr(32, 6),
		"SLDconst": shlc(64), "SRDconst": shrc(64), "SRADconst": shrc(64),
		"SLWconst": shlc(32), "SRWconst": shrc(32), "SRAWconst": shrc(32),
		"ADD": lo2(64), "ADDW": lo2(32), "ADDconst": lo1(64), "ADDWconst": lo1(32),
		"SUB": lo2(64), "SUBW": lo2(32), "SUBconst": lo1(64), "SUBWconst": lo1(32),
		"XOR": lo2(64), "XORW": lo2(32), "XORconst": lo1(64), "XORWconst": lo1(32),
		"NEG": lo1(64), "NEGW": lo1(32),
		"OR": or2(64), "ORW": or2(32), "ORconst": orc(64), "ORWconst": orc(32),
		"AND": and2(64), "ANDW": and2(32), "ANDconst": andc(64), "ANDWconst": andc(32),
		"MOVDconst": konst,
	},
	"Wasm": {
		"I64Extend8S": ext(8), "I64Extend16S": ext(16), "I64Extend32S": ext(32),
		"I64Ctz": ctz(64), "I64Clz": clz(64),
		"I64Shl": shl(64, 6), "I64ShrU": shr(64, 6), "I64ShrS": shr(64, 6),
		"I64Add": lo2(64), "I64Sub": lo2(64), "I64Xor": lo2(64),
		"I64Or": or2(64), "I64And": and2(64),
		"I64Const": konst,
	},
}
