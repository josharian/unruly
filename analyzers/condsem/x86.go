package condsem

import (
	"fmt"
	"math/bits"
	"strings"

	"github.com/josharian/unruly/ops"
)

// x86Conds are the x86 condition codes, by their Go assembler names
// (cmd/internal/obj/x86: JEQ, SETLT, CMOVQHI, ...), as functions of the
// flags. CS means the carry flag is set, which after a compare means an
// unsigned borrow.
var x86Conds = map[string]func(f *flags) tri{
	"EQ": func(f *flags) tri { return f.get(bZ) },
	"NE": func(f *flags) tri { return f.get(bZ).not() },
	"LT": func(f *flags) tri { return f.get(bNxV) },
	"GE": func(f *flags) tri { return f.get(bNxV).not() },
	"LE": func(f *flags) tri { return f.get(bZ).or(f.get(bNxV)) },
	"GT": func(f *flags) tri { return f.get(bZ).or(f.get(bNxV)).not() },
	"CS": func(f *flags) tri { return f.get(bC) },
	"CC": func(f *flags) tri { return f.get(bC).not() },
	"HI": func(f *flags) tri { return f.get(bC).or(f.get(bZ)).not() },
	"LS": func(f *flags) tri { return f.get(bC).or(f.get(bZ)) },
	"OS": func(f *flags) tri { return f.get(bV) },
	"OC": func(f *flags) tri { return f.get(bV).not() },
	"MI": func(f *flags) tri { return f.get(bN) },
	"PL": func(f *flags) tri { return f.get(bN).not() },
	"PS": func(f *flags) tri { return f.get(bP) },
	"PC": func(f *flags) tri { return f.get(bP).not() },
	// The float equality tests that codegen implements with two
	// instructions (amd64/ssa.go: SETEQF is SETEQ & SETPC, SETNEF is
	// SETNE | SETPS, and likewise CMOV*EQF, CMOV*NEF, and the EQF and NEF
	// blocks' eqfJumps and nefJumps).
	"EQF": func(f *flags) tri { return f.get(bZ).and(f.get(bP).not()) },
	"NEF": func(f *flags) tri { return f.get(bZ).not().or(f.get(bP)) },
}

func x86Cond(name string) *cond {
	f := x86Conds[name]
	if f == nil {
		return nil
	}
	cat := catInt
	switch name {
	case "EQ", "NE", "CS", "CC", "HI", "LS":
		cat = catBoth
	case "PS", "PC", "EQF", "NEF":
		cat = catFloat
	}
	return &cond{name: name, cat: cat, eval: f}
}

// x86Consts are the x86 flag constants (AMD64Ops.go): each records the
// signed and unsigned order of the compared values.
var x86Consts = map[string]struct{ eq, slt, ult bool }{
	"FlagEQ":     {eq: true},
	"FlagLT_ULT": {slt: true, ult: true},
	"FlagLT_UGT": {slt: true},
	"FlagGT_ULT": {ult: true},
	"FlagGT_UGT": {},
}

func computeX86(f *flags) {
	switch f.o {
	case oSub:
		subFlags(f, true)
	case oLogic:
		r := trunc(f.a, f.w)
		f.setBit(bZ, r == 0)
		f.setBit(bN, sext(r, f.w) < 0)
		f.setBit(bC, false)
		f.setBit(bV, false)
		f.setBit(bP, onesEven(r))
	case oFloat:
		// UCOMISS/UCOMISD set ZF, PF, CF and clear OF and SF.
		x, y := f.fa, f.fb
		un := x != x || y != y
		f.setBit(bZ, un || x == y)
		f.setBit(bP, un)
		f.setBit(bC, un || x < y)
		f.setBit(bN, false)
		f.setBit(bV, false)
	case oBitTest:
		// BT sets CF to the selected bit; ZF is unchanged and the
		// others are undefined.
		f.setBit(bC, f.a>>(f.b%uint64(f.w))&1 != 0)
		f.markStale(bZ, bN, bV, bP)
	}
}

func onesEven(r uint64) bool {
	n := 0
	for b := uint8(r); b != 0; b &= b - 1 {
		n++
	}
	return n%2 == 0
}

var x86Widths = map[string]uint8{"Q": 64, "L": 32, "W": 16, "B": 8}

func newX86(oa *ops.Arch) *arch {
	regW := uint8(64)
	if oa.Name == "386" {
		regW = 32
	}
	a := &arch{name: oa.Name, ptrW: regW, ops: map[string]*opSem{}, blocks: map[string]*blockSem{}, compute: computeX86}
	for _, name := range []string{"EQ", "NE", "LT", "GE", "LE", "GT", "CS", "CC", "HI", "LS", "OS", "OC", "MI", "PL", "PS", "PC", "EQF", "NEF"} {
		a.conds = append(a.conds, x86Cond(name))
	}
	has := func(name string) bool { return oa.Op(name) != nil }
	def := func(name string, s *opSem) {
		if has(name) {
			a.ops[name] = s
		}
	}
	for sfx, w := range x86Widths {
		w := w
		def("CMP"+sfx, &opSem{args: wInts(2, w), origin: oSub, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFlags(n.op, oSub, n.args[0].i, n.args[1].i, w))
		}})
		def("CMP"+sfx+"const", &opSem{args: wInts(1, w), origin: oSub, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFlags(n.op, oSub, n.args[0].i, uint64(n.auxInt()), w))
		}})
		def("TEST"+sfx, &opSem{args: wInts(2, w), origin: oLogic, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFlags(n.op, oLogic, n.args[0].i&n.args[1].i, 0, w))
		}})
		def("TEST"+sfx+"const", &opSem{args: wInts(1, w), origin: oLogic, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFlags(n.op, oLogic, n.args[0].i&uint64(n.auxInt()), 0, w))
		}})
		if w >= 32 {
			// BTQconst [c] x tests bit c of x; BTQ x y tests bit x%64 of y.
			def("BT"+sfx+"const", &opSem{args: wInts(1, w), origin: oBitTest, auxRange: rng(0, int64(w)-1), eval: func(c *ctx, n *node) val {
				return flagsVal(c.a.newFlags(n.op, oBitTest, n.args[0].i, uint64(n.auxInt()), w))
			}})
			def("BT"+sfx, &opSem{args: wInts(2, w), origin: oBitTest, eval: func(c *ctx, n *node) val {
				return flagsVal(c.a.newFlags(n.op, oBitTest, n.args[1].i, n.args[0].i, w))
			}})
		}
	}
	for _, sfx := range []string{"S", "D"} {
		w := uint8(32)
		if sfx == "D" {
			w = 64
		}
		def("UCOMIS"+sfx, &opSem{args: []want{wFloat(w), wFloat(w)}, origin: oFloat, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFloatFlags(n.op, n.args[0].f, n.args[1].f))
		}})
	}
	for _, name := range []string{"FlagEQ", "FlagLT_ULT", "FlagLT_UGT", "FlagGT_ULT", "FlagGT_UGT"} {
		k := x86Consts[name]
		f := &flags{op: name, o: oConst}
		f.setBit(bZ, k.eq)
		f.setBit(bNxV, k.slt)
		f.setBit(bC, k.ult)
		if has(name) {
			a.consts = append(a.consts, f)
		}
		def(name, &opSem{origin: oConst, eval: func(c *ctx, n *node) val { return flagsVal(f) }})
	}
	def("InvertFlags", &opSem{args: []want{wFlagsInv()}, inherit: true, eval: func(c *ctx, n *node) val {
		return flagsVal(c.a.invert(n.args[0].fl))
	}})

	// Flag consumers. The condition comes from the op's asm
	// (SETL's is SETLT), except for the two-instruction float tests.
	for _, op := range oa.Ops {
		name := op.Name
		var cname string
		switch {
		case strings.HasPrefix(name, "SET") && strings.HasPrefix(op.Asm, "SET"):
			cname = strings.TrimPrefix(op.Asm, "SET")
		case strings.HasPrefix(name, "CMOV") && strings.HasPrefix(op.Asm, "CMOV") && op.ArgLength == 3:
			cname = op.Asm[len("CMOVQ"):]
		default:
			continue
		}
		base := strings.TrimSuffix(strings.TrimSuffix(name, "store"), "idx1")
		switch {
		case strings.HasSuffix(base, "EQF"):
			cname = "EQF"
		case strings.HasSuffix(base, "NEF"):
			cname = "NEF"
		}
		cd := x86Cond(cname)
		if cd == nil {
			continue
		}
		cat := cd.cat
		if strings.HasSuffix(base, "F") {
			cat = catFloat
		} else if cat == catBoth {
			cat = catInt
		}
		switch {
		case strings.HasPrefix(name, "CMOV"):
			// CMOVQcc x y f is f satisfies cc ? y : x.
			a.ops[name] = &opSem{args: []want{wAny, wAny, wFlags(cat)}, eval: func(c *ctx, n *node) val {
				return pick(c, cd, n.args[2].fl, n.args[1], n.args[0])
			}}
		case strings.HasSuffix(name, "store"):
			// SETccstore [off] {sym} ptr f mem stores the condition's byte.
			a.ops[name] = &opSem{args: []want{wAny, wFlags(cat), wAny}, eval: func(c *ctx, n *node) val {
				return storeVal(n, n.args[0], intVal(b2u(test(c, cd, n.args[1].fl)), 8), n.args[2])
			}}
		case op.ArgLength == 1:
			a.ops[name] = &opSem{args: []want{wFlags(cat)}, eval: func(c *ctx, n *node) val {
				return intVal(b2u(test(c, cd, n.args[0].fl)), 8)
			}}
		}
	}
	for _, sfx := range []string{"Q", "L"} {
		w := x86Widths[sfx]
		// SBBQcarrymask f is -1 if the carry flag is set, else 0.
		def("SBB"+sfx+"carrymask", &opSem{args: []want{wFlags(catInt)}, eval: func(c *ctx, n *node) val {
			if test(c, x86Cond("CS"), n.args[0].fl) {
				return intVal(^uint64(0), w)
			}
			return intVal(0, w)
		}})
	}
	// Carry chains (AMD64Ops.go): ADCQ x y f is x+y+carry(f) and the
	// flags of that sum; SBBQ x y f is x-y-carry(f). NEGLflags x is -x
	// and its flags, whose carry is x != 0.
	carry := func(c *ctx, f *flags) uint64 { return b2u(test(c, x86Cond("CS"), f)) }
	arith := func(c *ctx, op string, x, y, cin uint64, sub bool) val {
		var r, cout uint64
		var ovf bool
		if sub {
			r, cout = bits.Sub64(x, y, cin)
			ovf = (int64(x) < 0) != (int64(y) < 0) && (int64(r) < 0) != (int64(x) < 0)
		} else {
			r, cout = bits.Add64(x, y, cin)
			ovf = (int64(x) < 0) == (int64(y) < 0) && (int64(r) < 0) != (int64(x) < 0)
		}
		f := &flags{op: op, o: oArith, a: x, b: y, w: 64}
		f.setBit(bZ, r == 0)
		f.setBit(bN, int64(r) < 0)
		f.setBit(bC, cout != 0)
		f.setBit(bV, ovf)
		f.setBit(bP, onesEven(r))
		return val{k: kTuple, xs: []val{intVal(r, 64), flagsVal(f)}}
	}
	def("ADCQ", &opSem{args: []want{wInt(64), wInt(64), wFlags(catInt)}, eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, n.args[1].i, carry(c, n.args[2].fl), false)
	}})
	def("ADCQconst", &opSem{args: []want{wInt(64), wFlags(catInt)}, eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, uint64(n.auxInt()), carry(c, n.args[1].fl), false)
	}})
	def("SBBQ", &opSem{args: []want{wInt(64), wInt(64), wFlags(catInt)}, eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, n.args[1].i, carry(c, n.args[2].fl), true)
	}})
	def("SBBQconst", &opSem{args: []want{wInt(64), wFlags(catInt)}, eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, uint64(n.auxInt()), carry(c, n.args[1].fl), true)
	}})
	def("ADDQcarry", &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, n.args[1].i, 0, false)
	}})
	def("ADDQconstcarry", &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, uint64(n.auxInt()), 0, false)
	}})
	def("SUBQborrow", &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, n.args[1].i, 0, true)
	}})
	def("SUBQconstborrow", &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val {
		return arith(c, n.op, n.args[0].i, uint64(n.auxInt()), 0, true)
	}})
	def("NEGLflags", &opSem{args: wInts(1, 32), eval: func(c *ctx, n *node) val {
		x := trunc(n.args[0].i, 32)
		f := c.a.newFlags(n.op, oSub, 0, x, 32)
		f.o = oArith
		return val{k: kTuple, xs: []val{intVal(trunc(-x, 32), regW), flagsVal(f)}}
	}})

	// Loads read a memory modeled as a function of the address and
	// the memory state. MOVLload and narrower zero-extend.
	for sfx, w := range x86Widths {
		w := w
		def("MOV"+sfx+"load", &opSem{args: []want{wAny, wAny}, eval: func(c *ctx, n *node) val {
			return intVal(c.load(n, n.args[0], n.auxint, n.args[1], w), regW)
		}})
		def("CMP"+sfx+"load", &opSem{args: []want{wAny, wInt(w), wAny}, origin: oSub, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFlags(n.op, oSub, c.load(n, n.args[0], n.auxint, n.args[2], w), n.args[1].i, w))
		}})
		def("CMP"+sfx+"constload", &opSem{args: []want{wAny, wAny}, origin: oSub, eval: func(c *ctx, n *node) val {
			vo := n.auxint
			if vo.k != gInt {
				unmodeled("%s aux %v", n.op, vo)
			}
			off := gv{k: gInt, i: uint64(int64(int32(vo.i)))}
			return flagsVal(c.a.newFlags(n.op, oSub, c.load(n, n.args[0], off, n.args[1], w), uint64(int64(vo.i)>>32), w))
		}})
	}
	def("MOVBstore", &opSem{args: []want{wAny, wInt(8), wAny}, eval: func(c *ctx, n *node) val {
		return storeVal(n, n.args[0], intVal(n.args[1].i, 8), n.args[2])
	}})

	// Integer ops. 32-bit ops zero the upper half of a 64-bit register.
	alu := func(name string, w uint8, f func(x, y uint64) uint64, auxRange *[2]int64) {
		rw := w
		if w == 32 {
			rw = regW
		}
		def(name, &opSem{args: wInts(2, w), eval: func(c *ctx, n *node) val {
			return intVal(trunc(f(n.args[0].i, n.args[1].i), w), rw)
		}})
		def(name+"const", &opSem{args: wInts(1, w), auxRange: auxRange, eval: func(c *ctx, n *node) val {
			return intVal(trunc(f(n.args[0].i, uint64(n.auxInt())), w), rw)
		}})
	}
	for _, sfx := range []string{"Q", "L"} {
		w := x86Widths[sfx]
		alu("ADD"+sfx, w, func(x, y uint64) uint64 { return x + y }, nil)
		alu("SUB"+sfx, w, func(x, y uint64) uint64 { return x - y }, nil)
		alu("AND"+sfx, w, func(x, y uint64) uint64 { return x & y }, nil)
		alu("OR"+sfx, w, func(x, y uint64) uint64 { return x | y }, nil)
		alu("XOR"+sfx, w, func(x, y uint64) uint64 { return x ^ y }, nil)
		// Shift counts are masked; constant shift amounts are in [0, w)
		// (AMD64Ops.go).
		mask := uint64(w - 1)
		sr := rng(0, int64(w)-1)
		alu("SHL"+sfx, w, func(x, y uint64) uint64 { return x << (y & mask) }, sr)
		alu("SHR"+sfx, w, func(x, y uint64) uint64 { return trunc(x, w) >> (y & mask) }, sr)
		alu("SAR"+sfx, w, func(x, y uint64) uint64 { return uint64(sext(x, w) >> (y & mask)) }, sr)
		rw := w
		if w == 32 {
			rw = regW
		}
		def("NEG"+sfx, &opSem{args: wInts(1, w), eval: func(c *ctx, n *node) val { return intVal(trunc(-n.args[0].i, w), rw) }})
		def("NOT"+sfx, &opSem{args: wInts(1, w), eval: func(c *ctx, n *node) val { return intVal(trunc(^n.args[0].i, w), rw) }})
		def("MOV"+sfx+"const", &opSem{eval: func(c *ctx, n *node) val { return intVal(trunc(uint64(n.auxInt()), w), rw) }})
	}
	for _, sfx := range []string{"W", "B"} {
		// 16- and 8-bit shifts leave the rest of the register alone.
		w := x86Widths[sfx]
		def("SHR"+sfx+"const", &opSem{args: wInts(1, w), auxRange: rng(0, int64(w)-1), eval: func(c *ctx, n *node) val {
			return intVal(trunc(n.args[0].i, w)>>uint64(n.auxInt()), w)
		}})
		def("SAR"+sfx+"const", &opSem{args: wInts(1, w), auxRange: rng(0, int64(w)-1), eval: func(c *ctx, n *node) val {
			return intVal(uint64(sext(n.args[0].i, w)>>uint64(n.auxInt())), w)
		}})
	}
	to := "Q"
	if regW == 32 {
		to = "L"
	}
	for _, from := range []string{"B", "W", "L"} {
		fw := x86Widths[from]
		def(fmt.Sprintf("MOV%s%sZX", from, to), &opSem{args: wInts(1, fw), eval: func(c *ctx, n *node) val { return intVal(trunc(n.args[0].i, fw), regW) }})
		def(fmt.Sprintf("MOV%s%sSX", from, to), &opSem{args: wInts(1, fw), eval: func(c *ctx, n *node) val {
			return intVal(uint64(sext(n.args[0].i, fw)), regW)
		}})
	}

	// Blocks. Their branches come from codegen's blockJump table.
	cg := parseCodegen(oa)
	for blk, asm := range cg.blockJump {
		if cd := x86Cond(asm); cd != nil && oa.Block(blk) != nil {
			defBlock(a, blk, cd, category(blk, "ULT", "ULE", "UGT", "UGE"))
		}
	}
	for _, blk := range []string{"EQF", "NEF"} {
		if oa.Block(blk) != nil {
			defBlock(a, blk, x86Cond(blk), catFloat)
		}
	}
	for _, sfx := range []string{"Q", "L", "W", "B"} {
		if has("CMP" + sfx) {
			a.producers = append(a.producers, producer{op: "CMP" + sfx, o: oSub, w: x86Widths[sfx]})
		}
	}
	for _, sfx := range []string{"Q", "L", "B"} {
		if has("TEST" + sfx) {
			a.producers = append(a.producers, producer{op: "TEST" + sfx, o: oLogic, w: x86Widths[sfx]})
		}
	}
	a.producers = append(a.producers, producer{op: "UCOMISD", o: oFloat})
	return a
}

func flagsVal(f *flags) val { return val{k: kFlags, fl: f} }

// test evaluates condition cd of flags f. A condition that reads flags
// the state doesn't define makes the state irrelevant on the match side
// and a mismatch on the result side; evalSide records which.
func test(c *ctx, cd *cond, f *flags) bool {
	t := cd.eval(f)
	switch t {
	case tTrue:
		return true
	case tFalse:
		return false
	case tStale:
		c.staleRead(cd, f)
	}
	impossible()
	return false
}

// pick returns x if f satisfies cd, else y.
func pick(c *ctx, cd *cond, f *flags, x, y val) val {
	if test(c, cd, f) {
		return x
	}
	return y
}

// storeVal returns a store of v to ptr+[auxint]+{aux}. With a known
// pointer value, the address is folded together, so that moving an offset
// between the pointer and the auxint doesn't change it.
func storeVal(n *node, ptr, v, mem val) val {
	if ptr.k == kInt && n.auxint.k == gInt {
		return val{k: kStore, s: fmt.Sprintf("{%v}", n.aux), xs: []val{intVal(ptr.i+n.auxint.i, ptr.w), v, mem}}
	}
	return val{k: kStore, s: fmt.Sprintf("[%v] {%v}", n.auxint, n.aux), xs: []val{ptr, v, mem}}
}

func defBlock(a *arch, name string, cd *cond, cat fcat) {
	a.blocks[name] = &blockSem{controls: []want{wFlags(cat)}, test: cd.name, eval: func(c *ctx, n *node) bool {
		return test(c, cd, n.args[0].fl)
	}}
}
