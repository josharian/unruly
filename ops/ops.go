// Package ops provides the SSA op and block tables that rulegen uses,
// loaded from a Go source tree's _gen directory.
//
// The tables are extracted by building the _gen package itself (see Load),
// so they are exactly what rulegen sees for that revision.
package ops

import (
	"fmt"
	"math/bits"
	"strings"
)

// Tables holds the op and block tables of one _gen directory.
type Tables struct {
	Dir   string  // the _gen directory
	Archs []*Arch // sorted by name; includes "generic" and the generic-family archs (dec, dec64, ...)

	// Generic is the "generic" arch. Its Ops and Blocks are rulegen's
	// genericOps and genericBlocks, which every arch's rules may use.
	Generic *Arch

	// ReservedNames are names that rulegen's generated code declares
	// itself (rulegen's reservedNames, such as "v" and "b"), which rules may
	// use but not bind. It is nil for revisions without reservedNames.
	ReservedNames map[string]bool

	byName map[string]*Arch
}

// Arch returns the arch with the given name (as in rulegen: "AMD64",
// "generic", "dec64", ...), or nil.
func (t *Tables) Arch(name string) *Arch { return t.byName[name] }

// Arch is one entry of rulegen's archs.
type Arch struct {
	Name string
	// Generic reports whether this is a machine-independent arch:
	// "generic" itself, or one whose rules rewrite generic ops into
	// generic ops (dec, dec64, divmod, divisible, ...).
	Generic bool
	Pkg     string // obj package, e.g. "cmd/internal/obj/x86"

	// Ops and Blocks are the arch-specific ops and blocks.
	// For non-generic arches they do not include the generic ones.
	Ops    []*Op
	Blocks []*Block

	RegNames []string

	GPRegMask      RegMask
	FPRegMask      RegMask
	FP32RegMask    RegMask
	FP64RegMask    RegMask
	SIMDRegMask    RegMask
	SIMDMaskRegs   RegMask // e.g. AMD64's K registers
	SpecialRegMask RegMask
	FramePointer   int // register number, or -1
	LinkReg        int // register number, or -1

	// Raw is the reflected dump of rulegen's arch struct, excluding ops
	// and blocks, for fields not modeled above.
	Raw map[string]any

	tables  *Tables
	opIdx   map[string]*Op
	blkIdx  map[string]*Block
	regIdx  map[string]int
	classes []classMask
}

// Tables returns the tables a belongs to.
func (a *Arch) Tables() *Tables { return a.tables }

// Op returns a's own op with the given name, or nil.
// It does not consult generic ops; see LookupOp.
func (a *Arch) Op(name string) *Op { return a.opIdx[name] }

// Block returns a's own block kind with the given name, or nil.
// It does not consult generic blocks; see LookupBlock.
func (a *Arch) Block(name string) *Block { return a.blkIdx[name] }

// LookupOp returns the op that name refers to in a rules file for a,
// ignoring argument counts: the generic op if there is one, else a's own.
// This mirrors rulegen's opIsCommutative and opByName.
func (a *Arch) LookupOp(name string) *Op {
	if op := a.tables.Generic.opIdx[name]; op != nil {
		return op
	}
	if a.Name == "generic" {
		return nil
	}
	return a.opIdx[name]
}

// ResolveOp returns the op that an s-expression (name arg...) with nargs
// arguments refers to in a rules file for a, mirroring rulegen's parseValue.
// An op matches if its name matches and it takes nargs arguments (or is
// variadic, or ellipsis is set, meaning the s-expression was (name ...)).
// Generic ops are searched first; it is an error for both a generic op and
// an arch op to match.
func (a *Arch) ResolveOp(name string, nargs int, ellipsis bool) (*Op, error) {
	fits := func(op *Op) bool {
		return op != nil && (op.ArgLength == -1 || int(op.ArgLength) == nargs || ellipsis)
	}
	var found *Op
	if op := a.tables.Generic.opIdx[name]; fits(op) {
		found = op
	}
	if a.Name != "generic" {
		if op := a.opIdx[name]; fits(op) {
			if found != nil {
				return nil, fmt.Errorf("matches for op %s found in both generic and %s", name, a.Name)
			}
			found = op
		}
	}
	if found != nil {
		return found, nil
	}
	if op := a.LookupOp(name); op != nil {
		return nil, fmt.Errorf("op %s (%s) should have %d args, has %d", name, op.Arch.Name, op.ArgLength, nargs)
	}
	return nil, fmt.Errorf("unknown op %s", name)
}

// LookupBlock returns the block kind that name refers to in a rules file
// for a: the generic block if there is one, else a's own. This mirrors
// rulegen's isBlock and getBlockInfo.
func (a *Arch) LookupBlock(name string) *Block {
	if b := a.tables.Generic.blkIdx[name]; b != nil {
		return b
	}
	return a.blkIdx[name]
}

// Reg returns the register number of the named register, or -1.
func (a *Arch) Reg(name string) int {
	if n, ok := a.regIdx[name]; ok {
		return n
	}
	return -1
}

// RegNamesOf returns the names of the registers in m.
func (a *Arch) RegNamesOf(m RegMask) []string {
	var names []string
	for _, r := range m.Regs() {
		if r < len(a.RegNames) {
			names = append(names, a.RegNames[r])
		} else {
			names = append(names, fmt.Sprintf("r%d", r))
		}
	}
	return names
}

// FormatRegMask formats m as a space-separated register list.
func (a *Arch) FormatRegMask(m RegMask) string {
	return strings.Join(a.RegNamesOf(m), " ")
}

// RegClass is a set of register classes.
type RegClass uint8

const (
	RegGP       RegClass = 1 << iota // in the arch's gpregmask
	RegFP                            // in fpregmask, fp32regmask, or fp64regmask
	RegSIMD                          // in simdregmask
	RegSIMDMask                      // in simdmaskreg (e.g. AMD64 K registers)
	RegOther                         // in none of the above (e.g. SP, SB, g, X15 on AMD64)
)

func (c RegClass) String() string {
	if c == 0 {
		return "none"
	}
	var s []string
	for i, name := range []string{"gp", "fp", "simd", "simdmask", "other"} {
		if c&(1<<i) != 0 {
			s = append(s, name)
		}
	}
	return strings.Join(s, "|")
}

type classMask struct {
	class RegClass
	mask  RegMask
}

// Classify returns the classes of the registers in m.
//
// Classes can overlap: on AMD64 and ARM64 the FP and SIMD masks contain the
// same registers, so an FP register mask classifies as RegFP|RegSIMD.
// An empty mask (as used for memory and flags inputs and outputs)
// classifies as 0; to tell those apart, consult the op's types.
func (a *Arch) Classify(m RegMask) RegClass {
	var c RegClass
	rest := m
	for _, cm := range a.classes {
		if !m.Intersect(cm.mask).Empty() {
			c |= cm.class
			rest = rest.Minus(cm.mask)
		}
	}
	if !rest.Empty() {
		c |= RegOther
	}
	return c
}

// Op is one entry of an arch's ops (rulegen's opData).
type Op struct {
	Name string
	Arch *Arch // the arch that defines the op; Tables.Generic for generic ops

	Asm       string
	Typ       string // default result type, e.g. "Int64", "Flags", "(UInt64,Flags)"; "" if none
	Aux       string // aux kind, e.g. "Int32", "SymOff"; "" if none
	ArgLength int32  // -1 for variadic

	Rematerializeable bool
	Commutative       bool // commutative in its first two arguments
	ResultInArg0      bool
	ResultNotInArgs   bool
	ClobberFlags      bool
	NeedIntTemp       bool
	Call              bool
	TailCall          bool
	NilCheck          bool
	FaultOnNilArg0    bool
	FaultOnNilArg1    bool
	HasSideEffects    bool
	ZeroWidth         bool
	UnsafePoint       bool
	FixedReg          bool
	EarlyOk           bool
	AddrSinkArg0      bool
	AddrSinkArg1      bool
	SymEffect         string // e.g. "Read", "Write", "Read,Write", "Addr"
	Scale             uint8
	ZeroUpperBits     uint8

	Reg RegInfo

	// SIMD reports whether a generic op is one of the machine-generated
	// SIMD ops (rulegen's additionalGenericOps).
	SIMD bool

	// AuxType and AuxIntType are the Go types rulegen uses for the op's
	// Aux and AuxInt fields (e.g. "Sym", "int32", "ValAndOff").
	// They are "invalid" if the op has no such field.
	AuxType    string
	AuxIntType string
	// HasAux and HasAuxInt report whether a rule may specify {aux} or
	// [auxint] for this op.
	HasAux    bool
	HasAuxInt bool

	// Raw is the reflected dump of rulegen's opData,
	// for fields not modeled above.
	Raw map[string]any
}

// IsGeneric reports whether op is a generic (machine-independent) op.
func (op *Op) IsGeneric() bool { return op.Arch.Name == "generic" }

// QualifiedName returns the name of op's Op constant without the "Op"
// prefix, e.g. "AMD64ADDQ" or "Add64".
func (op *Op) QualifiedName() string {
	if op.IsGeneric() {
		return op.Name
	}
	return op.Arch.Name + op.Name
}

func (op *Op) String() string { return op.QualifiedName() }

// TupleTypes splits a tuple default type such as "(UInt64,Flags)" into
// its elements. It returns nil if Typ is not a tuple.
func (op *Op) TupleTypes() []string {
	if !strings.HasPrefix(op.Typ, "(") {
		return nil
	}
	return strings.Split(op.Typ[1:len(op.Typ)-1], ",")
}

// RegInfo is an op's register constraints (rulegen's regInfo).
type RegInfo struct {
	// Inputs[i] is the set of registers allowed for argument i.
	// It is empty for arguments that don't use registers (memory, flags).
	// Trailing such arguments may be omitted entirely.
	Inputs       []RegMask
	Outputs      []RegMask
	Clobbers     RegMask
	ClobbersArg0 bool
	ClobbersArg1 bool
}

// Block is one entry of an arch's blocks (rulegen's blockData).
type Block struct {
	Name     string
	Arch     *Arch
	Controls int    // number of control values
	Aux      string // aux kind, "" if none

	// AuxType and AuxIntType are the Go types rulegen uses for the
	// block's Aux and AuxInt fields, "invalid" if none.
	AuxType    string
	AuxIntType string

	Raw map[string]any
}

// IsGeneric reports whether b is a generic block kind.
func (b *Block) IsGeneric() bool { return b.Arch.Name == "generic" }

// QualifiedName returns the name of b's Block constant without the
// "Block" prefix, e.g. "AMD64EQ" or "If".
func (b *Block) QualifiedName() string {
	if b.IsGeneric() {
		return b.Name
	}
	return b.Arch.Name + b.Name
}

func (b *Block) String() string { return b.QualifiedName() }

// RegMask is a set of registers, numbered as in Arch.RegNames.
type RegMask struct {
	Lo, Hi uint64 // registers 0-63 and 64-127
}

// RegMaskOf returns the mask containing exactly the given registers.
func RegMaskOf(regs ...int) RegMask {
	var m RegMask
	for _, r := range regs {
		m = m.Add(r)
	}
	return m
}

func (m RegMask) Empty() bool { return m.Lo == 0 && m.Hi == 0 }

func (m RegMask) Has(r int) bool {
	if r < 64 {
		return m.Lo>>r&1 != 0
	}
	return m.Hi>>(r-64)&1 != 0
}

func (m RegMask) Add(r int) RegMask {
	if r < 64 {
		m.Lo |= 1 << r
	} else {
		m.Hi |= 1 << (r - 64)
	}
	return m
}

func (m RegMask) Union(n RegMask) RegMask     { return RegMask{m.Lo | n.Lo, m.Hi | n.Hi} }
func (m RegMask) Intersect(n RegMask) RegMask { return RegMask{m.Lo & n.Lo, m.Hi & n.Hi} }
func (m RegMask) Minus(n RegMask) RegMask     { return RegMask{m.Lo &^ n.Lo, m.Hi &^ n.Hi} }
func (m RegMask) SubsetOf(n RegMask) bool     { return m.Minus(n).Empty() }
func (m RegMask) Count() int                  { return bits.OnesCount64(m.Lo) + bits.OnesCount64(m.Hi) }

// Regs returns the register numbers in m, in increasing order.
func (m RegMask) Regs() []int {
	var r []int
	for i := range 128 {
		if m.Has(i) {
			r = append(r, i)
		}
	}
	return r
}

// TypeExpr returns the Go expression rulegen generates for a type name
// used as an op's default type, mirroring rulegen's typeName.
// For example, "UInt64" yields "typ.UInt64", "Flags" yields "types.TypeFlags",
// and "(UInt64,Flags)" yields a types.NewTuple call.
func TypeExpr(typ string) string {
	if strings.HasPrefix(typ, "(") {
		ts := strings.Split(typ[1:len(typ)-1], ",")
		if len(ts) != 2 {
			return "invalid tuple " + typ
		}
		return "types.NewTuple(" + TypeExpr(ts[0]) + ", " + TypeExpr(ts[1]) + ")"
	}
	switch typ {
	case "Flags", "Mem", "Void", "Int128":
		return "types.Type" + typ
	}
	return "typ." + typ
}
