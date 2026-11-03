package extelim

import (
	"fmt"
	"go/ast"
	"go/parser"
	"math/bits"
	"regexp"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// A fact is what is known about the bits of a register holding a value:
// the value is zero-extended from its low zm bits (it is < 1<<zm as an
// unsigned number) and sign-extended from its low sm bits. A fact of
// {64, 64} (or {32, 32} on a 32-bit arch) says nothing.
type fact struct{ zm, sm int }

func mkFact(zm, sm int) fact {
	zm, sm = max(zm, 0), max(sm, 1)
	return fact{zm, min(sm, zm+1)}
}

func zeroFrom(n int) fact { return mkFact(n, 64) }
func signFrom(n int) fact { return mkFact(64, n) }

// constFact is the fact of a register holding exactly c.
func constFact(c int64) fact {
	if c >= 0 {
		return mkFact(bits.Len64(uint64(c)), 64)
	}
	return mkFact(64, bits.Len64(uint64(^c))+1)
}

func (f fact) join(g fact) fact { return mkFact(max(f.zm, g.zm), max(f.sm, g.sm)) }

// cap limits f to regBits: on a 32-bit arch nothing above bit 31 exists.
func (f fact) cap(regBits int) fact { return mkFact(min(f.zm, regBits), min(f.sm, regBits)) }

// An ext is an extension op's effect: sign- or zero-extend the low w bits.
type ext struct {
	signed bool
	w      int
}

func (e ext) String() string {
	if e.signed {
		return fmt.Sprintf("sign-extends from %d bits", e.w)
	}
	return fmt.Sprintf("zero-extends from %d bits", e.w)
}

func (e ext) fact() fact {
	if e.signed {
		return signFrom(e.w)
	}
	return zeroFrom(e.w)
}

// holds reports whether a value with fact f is unchanged by e.
func (f fact) holds(e ext) bool {
	if e.signed {
		return f.sm <= e.w
	}
	return f.zm <= e.w
}

func (f fact) String() string {
	switch {
	case f.zm < 64 && f.zm+1 == f.sm:
		return fmt.Sprintf("zero-extended from %d bits", f.zm)
	case f.sm < 64:
		return fmt.Sprintf("sign-extended from %d bits", f.sm)
	}
	return "not extended"
}

// An archInfo describes what an arch's registers hold.
type archInfo struct {
	name    string
	regBits int
	// exts are the arch's extension ops.
	exts map[string]ext
	// moves are register-to-register copies, which preserve every bit.
	moves map[string]bool
	// restoreZero reports that regalloc restores a spilled value with a
	// zero-extending load of the value's size whatever its type's
	// signedness. Otherwise it extends by the type's signedness.
	restoreZero bool
	// mnemonics give the extension done by a load or extension op with
	// that Asm, for ops matching extLoadRE.
	mnemonics map[string]ext
	// facts give the facts of other ops. They are consulted before
	// mnemonics and an op's zeroUpperBits attribute.
	facts map[string]factFunc
	// select0 gives the fact of Select0 of a tuple op.
	select0 map[string]fact
	// auxRange gives the documented range of an op's auxint, for ops
	// whose fact depends on it.
	auxRange map[string][2]int64
}

// extLoadRE matches the ops to which archInfo.mnemonics apply: plain loads
// (not atomic loads, whose mnemonics differ in meaning on x86), and
// extension ops.
var extLoadRE = regexp.MustCompile(`^MOV[A-Z]*(load|loadidx[0-9]*|reg|[QL][SZ]X)$`)

// A factFunc computes the fact of a match node from the node, its auxint
// (if known), and its args' facts.
type factFunc func(fc *factCtx) fact

type factCtx struct {
	n    *rules.Value
	aux  val // the node's auxint, kUnknown if not known
	args []fact
	top  fact
	// auxUnknown records that the fact needed the auxint but it was
	// not known, so the fact is only a bound.
	auxUnknown bool
}

func (fc *factCtx) auxInt() (int64, bool) {
	if fc.aux.k.isInt() {
		return fc.aux.i, true
	}
	fc.auxUnknown = true
	return 0, false
}

// Common fact functions.

func always(f fact) factFunc { return func(*factCtx) fact { return f } }

// boolResult: the op computes 0 or 1 in the whole register.
var boolResult = always(zeroFrom(1))

// andConst: arg0 & auxint, computed in the whole register.
func andConst(fc *factCtx) fact {
	f := fc.args[0]
	if c, ok := fc.auxInt(); ok && c >= 0 {
		f = mkFact(min(f.zm, bits.Len64(uint64(c))), max(f.sm, 1))
	}
	return f
}

// andRegs: arg0 & arg1, computed in the whole register.
func andRegs(fc *factCtx) fact {
	return mkFact(min(fc.args[0].zm, fc.args[1].zm), max(fc.args[0].sm, fc.args[1].sm))
}

// srl32 is a logical right shift by auxint of the low 32 bits whose
// 32-bit result is then zero-extended (zext) or sign-extended (!zext).
func srl32(zext bool) factFunc {
	return func(fc *factCtx) fact {
		c, ok := fc.auxInt()
		if !ok {
			if zext {
				return zeroFrom(32)
			}
			return signFrom(32)
		}
		c &= 31
		in := min(fc.args[0].zm, 32)
		if c == 0 && in == 32 && !zext {
			return signFrom(32)
		}
		return zeroFrom(in - int(c))
	}
}

// sra32 is an arithmetic right shift by auxint of the low 32 bits,
// sign-extended to 64 bits.
func sra32(fc *factCtx) fact {
	c, ok := fc.auxInt()
	if !ok {
		return signFrom(32)
	}
	c &= 31
	in := fc.args[0]
	f := signFrom(min(in.sm, 32) - int(c))
	if in.zm < 32 {
		f = mkFact(in.zm-int(c), f.sm)
	}
	return f
}

// srl64 is a 64-bit logical right shift by auxint.
func srl64(fc *factCtx) fact {
	c, ok := fc.auxInt()
	if !ok {
		return fc.top
	}
	return zeroFrom(fc.args[0].zm - int(c&63))
}

// sra64 is a 64-bit arithmetic right shift by auxint.
func sra64(fc *factCtx) fact {
	c, ok := fc.auxInt()
	if !ok {
		return fc.top
	}
	in := fc.args[0]
	zm := 64
	if in.zm < 64 {
		zm = in.zm - int(c&63)
	}
	return mkFact(zm, in.sm-int(c&63))
}

// bitfield extracts aux.Width() bits, zero- or sign-extending them
// (ARM64 UBFX and SBFX).
func bitfield(signed bool) factFunc {
	return func(fc *factCtx) fact {
		c, ok := fc.auxInt()
		if !ok {
			return fc.top
		}
		w := int(c & 0xff)
		if signed {
			return signFrom(w)
		}
		return zeroFrom(w)
	}
}

// selectArgs: the result is one of the args (a conditional select).
func selectArgs(fc *factCtx) fact {
	return fc.args[0].join(fc.args[1])
}

// constOp is a constant. If its value is not known, its auxint expression
// may still show its range: [int64(uint32(x))] is zero-extended from 32 bits.
func constOp(fc *factCtx) fact {
	if c, ok := fc.auxInt(); ok {
		return constFact(c)
	}
	x, err := parser.ParseExpr(fc.n.AuxInt)
	if err != nil {
		return fc.top
	}
	fc.auxUnknown = false // the expression's form is the fact
	return exprFact(x)
}

// exprFact returns what the form of the integer expression x says about its
// value: the conversions it is wrapped in, and the result types of the
// read helpers.
func exprFact(x ast.Expr) fact {
	top := fact{64, 64}
	call, ok := x.(*ast.CallExpr)
	if !ok {
		return top
	}
	_, name := funcName(call.Fun)
	switch name {
	case "b2i", "b2i32":
		return zeroFrom(1)
	case "read8":
		return zeroFrom(8)
	case "read16":
		return zeroFrom(16)
	case "read32":
		return zeroFrom(32)
	}
	k, ok := kindNames[name]
	if !ok || k == kBitField || len(call.Args) != 1 {
		return top
	}
	f := exprFact(call.Args[0])
	if k.bits() == 64 {
		return f
	}
	e := ext{k.signed(), int(k.bits())}
	if f.holds(e) {
		return f
	}
	return e.fact()
}

// Extension ops and extending loads, by mnemonic.
var (
	s8, z8, s16, z16, s32, z32 = ext{true, 8}, ext{false, 8}, ext{true, 16}, ext{false, 16}, ext{true, 32}, ext{false, 32}

	// The common RISC spelling: MOVB/MOVH/MOVW sign-extend into a
	// 64-bit register, MOVBU/MOVHU/MOVWU zero-extend. (ARM64: ldrsb/
	// ldrb/sxtb/uxtb...; LOONG64: ld.b/ld.bu/ext.w.b...; MIPS64: lb/lbu...;
	// RISCV64: lb/lbu...)
	riscMnemonics = map[string]ext{"MOVB": s8, "MOVBU": z8, "MOVH": s16, "MOVHU": z16, "MOVW": s32, "MOVWU": z32}
	// 32-bit ARM and MIPS: MOVW is a full-register move.
	risc32Mnemonics = map[string]ext{"MOVB": s8, "MOVBS": s8, "MOVBU": z8, "MOVH": s16, "MOVHS": s16, "MOVHU": z16}
	// PPC64 and S390X use Z for zero extension. PPC64's MOVHBR and
	// MOVWBR are lhbrx and lwbrx, which zero-extend.
	ppcMnemonics  = map[string]ext{"MOVB": s8, "MOVBZ": z8, "MOVH": s16, "MOVHZ": z16, "MOVW": s32, "MOVWZ": z32, "MOVHBR": z16, "MOVWBR": z32}
	s390Mnemonics = map[string]ext{"MOVB": s8, "MOVBZ": z8, "MOVH": s16, "MOVHZ": z16, "MOVW": s32, "MOVWZ": z32}
	// x86: a 32-bit destination zeroes the upper half of a 64-bit
	// register, so MOVL and MOVBLZX zero-extend on AMD64.
	amd64Mnemonics = map[string]ext{"MOVBLZX": z8, "MOVWLZX": z16, "MOVL": z32, "MOVBQSX": s8, "MOVWQSX": s16, "MOVLQSX": s32}
	x86Mnemonics   = map[string]ext{"MOVBLZX": z8, "MOVWLZX": z16, "MOVBLSX": s8, "MOVWLSX": s16}
)

func riscExts(w32 bool) map[string]ext {
	m := map[string]ext{"MOVBreg": s8, "MOVBUreg": z8, "MOVHreg": s16, "MOVHUreg": z16}
	if w32 {
		m["MOVWreg"], m["MOVWUreg"] = s32, z32
	}
	return m
}

var zExts = map[string]ext{"MOVBreg": s8, "MOVBZreg": z8, "MOVHreg": s16, "MOVHZreg": z16, "MOVWreg": s32, "MOVWZreg": z32}

// archs describes the arches whose rules have extension ops.
//
// Sources: restoreZero and the restore extension come from loadByType
// (loadByRegWidth on amd64) in cmd/compile/internal/<arch>/ssa.go. Op
// semantics come from the op comments in _gen/<arch>Ops.go and the
// instruction each op assembles to.
var archs = map[string]*archInfo{
	"AMD64": {
		regBits:     64,
		exts:        map[string]ext{"MOVBQSX": s8, "MOVBQZX": z8, "MOVWQSX": s16, "MOVWQZX": z16, "MOVLQSX": s32, "MOVLQZX": z32},
		restoreZero: true, // MOVBLZX, MOVWLZX, MOVL
		mnemonics:   amd64Mnemonics,
		facts: map[string]factFunc{
			"MOVQconst": constOp,
			// ANDL zeroes the upper half.
			"ANDLconst": func(fc *factCtx) fact {
				f := andConst(fc)
				return mkFact(min(f.zm, 32), f.sm)
			},
			"ANDQconst": andConst,
			"MOVLconst": func(fc *factCtx) fact { // MOVL $c zeroes the upper half
				if c, ok := fc.auxInt(); ok {
					return constFact(int64(uint32(c)))
				}
				if f := constOp(fc); f.zm <= 32 {
					return f
				}
				return zeroFrom(32)
			},
		},
	},
	"386": {
		regBits:     32,
		exts:        map[string]ext{"MOVBLSX": s8, "MOVBLZX": z8, "MOVWLSX": s16, "MOVWLZX": z16},
		restoreZero: true, // MOVBLZX, MOVWLZX
		mnemonics:   x86Mnemonics,
		facts:       map[string]factFunc{"MOVLconst": constOp, "ANDLconst": andConst},
	},
	"ARM": {
		regBits:   32,
		exts:      riscExts(false),
		moves:     map[string]bool{"MOVWreg": true, "MOVWnop": true},
		mnemonics: risc32Mnemonics,
		facts:     map[string]factFunc{"MOVWconst": constOp, "ANDconst": andConst, "AND": andRegs},
	},
	"MIPS": {
		regBits:   32,
		exts:      riscExts(false),
		moves:     map[string]bool{"MOVWreg": true, "MOVWnop": true},
		mnemonics: risc32Mnemonics,
		facts:     map[string]factFunc{"MOVWconst": constOp, "ANDconst": andConst, "AND": andRegs},
	},
	"ARM64": {
		regBits:   64,
		exts:      riscExts(true),
		moves:     map[string]bool{"MOVDreg": true, "MOVDnop": true},
		mnemonics: riscMnemonics,
		facts: map[string]factFunc{
			"MOVDconst": constOp,
			"ANDconst":  andConst,
			"AND":       andRegs,
			// UBFX/SBFX extract aux.Width() bits.
			"UBFX": bitfield(false),
			"SBFX": bitfield(true),
			// arm64/ssa.go: "generate boolean values using CSET".
			"Equal": boolResult, "NotEqual": boolResult,
			"LessThan": boolResult, "LessEqual": boolResult, "GreaterThan": boolResult, "GreaterEqual": boolResult,
			"LessThanU": boolResult, "LessEqualU": boolResult, "GreaterThanU": boolResult, "GreaterEqualU": boolResult,
			"LessThanF": boolResult, "LessEqualF": boolResult, "GreaterThanF": boolResult, "GreaterEqualF": boolResult,
			"NotLessThanF": boolResult, "NotLessEqualF": boolResult, "NotGreaterThanF": boolResult, "NotGreaterEqualF": boolResult,
			"LessThanNoov": boolResult, "GreaterEqualNoov": boolResult,
			// SIMD element extraction (arm64/simdssa.go simdVgpImmIn1;
			// obj/arm64 asm7.go case 73): VMOV is UMOV to a W register,
			// which zero-extends; VSMOV is SMOV to an X register.
			"VMOVBextr": always(zeroFrom(8)), "VMOVHextr": always(zeroFrom(16)), "VMOVSextr": always(zeroFrom(32)),
			"VSMOVBextr": always(signFrom(8)), "VSMOVHextr": always(signFrom(16)), "VSMOVSextr": always(signFrom(32)),
		},
	},
	"LOONG64": {
		regBits:   64,
		exts:      riscExts(true),
		moves:     map[string]bool{"MOVVreg": true, "MOVVnop": true},
		mnemonics: riscMnemonics,
		facts: map[string]factFunc{
			"MOVVconst": constOp,
			"ANDconst":  andConst,
			"AND":       andRegs,
			// SRL $c is srli.w: the low word shifted right, then
			// sign-extended from bit 31.
			"SRLconst": srl32(false),
			// "1 if arg0 > arg1, 0 otherwise". (Their zeroUpperBits
			// attribute, 56, says less.)
			"SGT": boolResult, "SGTU": boolResult, "SGTconst": boolResult, "SGTUconst": boolResult,
		},
		// LOONG64Ops.go: "auxInt should be in the range 0 to 31".
		auxRange: map[string][2]int64{"SRLconst": {0, 31}},
	},
	"MIPS64": {
		regBits:   64,
		exts:      riscExts(true),
		moves:     map[string]bool{"MOVVreg": true, "MOVVnop": true},
		mnemonics: riscMnemonics,
		facts:     map[string]factFunc{"MOVVconst": constOp, "ANDconst": andConst, "AND": andRegs},
	},
	"RISCV64": {
		regBits:   64,
		exts:      riscExts(true),
		moves:     map[string]bool{"MOVDreg": true, "MOVDnop": true},
		mnemonics: riscMnemonics,
		facts: map[string]factFunc{
			"MOVDconst": constOp,
			"ANDI":      andConst,
			"AND":       andRegs,
			"SRLI":      srl64,
			// SRLIW: "logical right shift of 32 bit value, sign extended
			// to 64 bits". At shift 0 that is a sign extension.
			"SRLIW": srl32(false),
			"SRAIW": sra32,
			// W ops compute on the low word and sign-extend the result.
			"ADDIW": always(signFrom(32)), "NEGW": always(signFrom(32)), "SUBW": always(signFrom(32)),
			"MULW": always(signFrom(32)), "DIVW": always(signFrom(32)), "DIVUW": always(signFrom(32)),
			"REMW": always(signFrom(32)), "REMUW": always(signFrom(32)),
			"SLLW": always(signFrom(32)), "SRAW": always(signFrom(32)), "SRLW": always(signFrom(32)), "SLLIW": always(signFrom(32)),
			"ROLW": always(signFrom(32)), "RORW": always(signFrom(32)), "RORIW": always(signFrom(32)),
			// Set-on-condition ops: "result is 0 or 1".
			"SEQZ": boolResult, "SNEZ": boolResult, "SLT": boolResult, "SLTI": boolResult, "SLTU": boolResult, "SLTIU": boolResult,
			"FEQS": boolResult, "FNES": boolResult, "FLTS": boolResult, "FLES": boolResult,
			"FEQD": boolResult, "FNED": boolResult, "FLTD": boolResult, "FLED": boolResult,
		},
		// RISCV64Ops.go: "shift amount 0-63" (SRLI), "0-31" (the W forms).
		auxRange: map[string][2]int64{"SRLI": {0, 63}, "SRLIW": {0, 31}, "SRAIW": {0, 31}},
		// riscv64/ssa.go: LoweredAtomicLoad8 is MOVBU, LoweredAtomicLoad32
		// is LR.W (sign-extending), and LoweredAtomicCas* leave 0 or 1.
		select0: map[string]fact{
			"LoweredAtomicLoad8":  zeroFrom(8),
			"LoweredAtomicLoad32": signFrom(32),
			"LoweredAtomicCas32":  zeroFrom(1),
			"LoweredAtomicCas64":  zeroFrom(1),
		},
	},
	"PPC64": {
		regBits:   64,
		exts:      zExts,
		mnemonics: ppcMnemonics,
		facts: map[string]factFunc{
			"MOVDconst": constOp,
			"ANDconst":  andConst,
			"AND":       andRegs,
			// SRW, SRAW, and SLW with a constant are rlwinm/srawi forms,
			// which compute a 32-bit result and zero- (rlwinm) or
			// sign-extend (srawi) it.
			"SRWconst":  srl32(true),
			"SRAWconst": sra32,
			"SLWconst":  always(zeroFrom(32)),
			"SRDconst":  srl64,
			"SRADconst": sra64,
		},
		// PPC64Ops.go: "0 <= auxInt < 32" for the W shifts, 64 for the D shifts.
		auxRange: map[string][2]int64{"SRWconst": {0, 31}, "SRAWconst": {0, 31}, "SLWconst": {0, 31}, "SRDconst": {0, 63}, "SRADconst": {0, 63}},
		// ppc64/ssa.go: LoweredAtomicLoad8 and 32 load with MOVBZ and MOVWZ.
		select0: map[string]fact{
			"LoweredAtomicLoad8":  zeroFrom(8),
			"LoweredAtomicLoad32": zeroFrom(32),
		},
	},
	"S390X": {
		regBits:   64,
		exts:      zExts,
		mnemonics: s390Mnemonics,
		facts: map[string]factFunc{
			"MOVDconst": constOp,
			"ANDconst":  andConst,
			"AND":       andRegs,
			// LOCGR is a conditional move: the result is one of its args.
			"LOCGR": selectArgs,
		},
	},
}

// A factSrc says how much an opFact can be trusted.
type factSrc int

const (
	srcNone  factSrc = iota // the op is not modeled
	srcBound                // a bound: the register may be more extended than this (zeroUpperBits)
	srcExact                // the op's documented result
)

func init() {
	for name, a := range archs {
		a.name = name
	}
}

// opFact computes the fact of the match node n in world w.
func (a *archInfo) opFact(n *rules.Value, w world) (fact, factSrc) {
	top := fact{a.regBits, a.regBits}
	if n.Op == nil {
		if f, ok := w.leaf[n.Name]; ok {
			return f, srcExact
		}
		if m := w.bound[n.Name]; m != nil {
			return a.opFact(m, w)
		}
		return top, srcExact // a variable: anything
	}
	var aux val
	switch {
	case n.AuxInt == "":
	case rules.IsVarText(n.AuxInt):
		aux = w.env[n.AuxInt]
	default:
		aux = evalString(n.AuxInt, w.env)
	}
	if aux.k == kUntyped {
		aux.k = kInt64
	}
	typ, typOK := w.typeOf(n)
	name := n.Op.Name
	switch {
	case name == "Arg":
		// Args are loaded from the stack as regalloc would restore
		// them (see rewrite.go's zeroUpperBits).
		if !typOK {
			return top, srcBound
		}
		return a.restored(typ, top), srcExact
	case name == "Select0" && len(n.Args) == 1 && n.Args[0].Op != nil:
		if f, ok := a.select0[n.Args[0].Op.Name]; ok {
			return f.cap(a.regBits), srcExact
		}
		return top, srcNone
	}
	if n.Op.IsGeneric() {
		return top, srcNone
	}
	if a.moves[name] && len(n.Args) == 1 {
		return a.opFact(n.Args[0], w)
	}
	if ff := a.facts[name]; ff != nil {
		fc := &factCtx{n: n, aux: aux, top: top}
		src := srcExact
		for _, arg := range n.Args {
			f, s := a.opFact(arg, w)
			if s == srcNone {
				f = top
			}
			src = min(src, max(s, srcBound))
			fc.args = append(fc.args, f)
		}
		f := ff(fc).cap(a.regBits)
		if fc.auxUnknown {
			src = min(src, srcBound)
		}
		return f, src
	}
	if e, ok := a.mnemonics[n.Op.Asm]; ok && extLoadRE.MatchString(name) {
		return e.fact().cap(a.regBits), srcExact
	}
	if z := int(n.Op.ZeroUpperBits); z > 0 {
		return zeroFrom(64 - z).cap(a.regBits), srcBound
	}
	if a.name == "AMD64" && writes32(n.Op) {
		// Intel SDM vol. 1, 3.4.1.1: "32-bit operands generate a 32-bit
		// result, zero-extended to a 64-bit result in the destination
		// general-purpose register."
		return zeroFrom(32), srcExact
	}
	return top, srcNone
}

// writes32 reports whether op computes a single 32-bit result into a
// general-purpose register (an L-suffixed instruction). BSF and BSR leave
// their destination unchanged when the input is zero.
func writes32(op *ops.Op) bool {
	if !strings.HasSuffix(op.Asm, "L") || op.Asm == "BSFL" || op.Asm == "BSRL" || len(op.Reg.Outputs) != 1 {
		return false
	}
	return op.Arch.Classify(op.Reg.Outputs[0]) == ops.RegGP
}

// validAux reports whether the auxints of n and its args in w are in the
// ranges their ops document.
func (a *archInfo) validAux(n *rules.Value, w world) bool {
	ok := true
	n.Walk(func(m *rules.Value) bool {
		if m.Op == nil || !rules.IsVarText(m.AuxInt) {
			return ok
		}
		r, has := a.auxRange[m.Op.Name]
		if v := w.env[m.AuxInt]; has && v.k.isInt() && (v.i < r[0] || v.i > r[1]) {
			ok = false
		}
		return ok
	})
	return ok
}

// restored returns the fact of a register restored from a spill of a value
// of type t: regalloc reloads it with a load of t's size that extends by t's
// signedness (or always zero-extends, if restoreZero).
func (a *archInfo) restored(t ssaType, top fact) fact {
	n := int(t.size()) * 8
	if n >= a.regBits {
		return top
	}
	if a.restoreZero || !t.signed() {
		return zeroFrom(n)
	}
	return signFrom(n)
}

// survivesSpill reports whether a register with fact f, holding a value of
// type t, holds the same bits after a spill and restore.
func (a *archInfo) survivesSpill(f fact, t ssaType) bool {
	n := int(t.size()) * 8
	if n >= a.regBits {
		return true
	}
	if a.restoreZero || !t.signed() {
		return f.zm <= n
	}
	return f.sm <= n
}
