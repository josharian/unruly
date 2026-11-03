package condsem

import (
	"math/bits"

	"github.com/josharian/unruly/ops"
)

// armConds are the ARM and ARM64 condition codes (the Arm Architecture
// Reference Manual's condition code table), as functions of NZCV.
// After a compare, C means no unsigned borrow.
var armConds = map[string]func(f *flags) tri{
	"EQ": armEQ,
	"NE": func(f *flags) tri { return armEQ(f).not() },
	"HS": func(f *flags) tri { return f.get(bC) },
	"CS": func(f *flags) tri { return f.get(bC) },
	"LO": func(f *flags) tri { return f.get(bC).not() },
	"CC": func(f *flags) tri { return f.get(bC).not() },
	"MI": func(f *flags) tri { return f.get(bN) },
	"PL": func(f *flags) tri { return f.get(bN).not() },
	"VS": func(f *flags) tri { return f.get(bV) },
	"VC": func(f *flags) tri { return f.get(bV).not() },
	"HI": func(f *flags) tri { return armLS(f).not() },
	"LS": armLS,
	"GE": func(f *flags) tri { return armLT(f).not() },
	"LT": armLT,
	"GT": func(f *flags) tri { return armLE(f).not() },
	"LE": armLE,
	// LEnoov and GTnoov branch on two conditions (arm64/ssa.go and
	// arm/ssa.go leJumps and gtJumps): EQ or MI, and neither.
	"LEnoov": func(f *flags) tri { return f.get(bZ).or(f.get(bN)) },
	"GTnoov": func(f *flags) tri { return f.get(bZ).or(f.get(bN)).not() },
}

func armCond(name string, cat fcat) *cond {
	f := armConds[name]
	if f == nil {
		return nil
	}
	return &cond{name: name, cat: cat, eval: f}
}

// computeARM computes NZCV. On ARM64 a logical op with flags (TST, ANDS)
// clears C and V; on ARM, TST and TEQ leave V alone and set C from the
// shifter, so both hold whatever an earlier instruction left.
func computeARM(arm64 bool) func(f *flags) {
	return func(f *flags) {
		switch f.o {
		case oSub:
			subFlags(f, false)
		case oAdd:
			addFlags(f)
		case oLogic:
			r := trunc(f.a, f.w)
			f.setBit(bZ, r == 0)
			f.setBit(bN, sext(r, f.w) < 0)
			if arm64 {
				f.setBit(bC, false)
				f.setBit(bV, false)
			} else {
				f.markStale(bC, bV)
			}
		case oFloat:
			// FCMP (ARM64) and VCMP+VMRS (ARM): unordered is 0011, equal
			// 0110, less 1000, greater 0010.
			x, y := f.fa, f.fb
			un := x != x || y != y
			f.setBit(bN, !un && x < y)
			f.setBit(bZ, !un && x == y)
			f.setBit(bC, un || x >= y)
			f.setBit(bV, un)
		}
	}
}

// shift applies an ARM shifted-operand shift to y.
func armShift(kind string, y, s uint64, w uint8) uint64 {
	y = trunc(y, w)
	switch kind {
	case "LL":
		if s >= uint64(w) {
			return 0
		}
		return trunc(y<<s, w)
	case "RL":
		if s >= uint64(w) {
			return 0
		}
		return y >> s
	case "RA":
		if s >= uint64(w) {
			s = uint64(w) - 1
		}
		return trunc(uint64(sext(y, w)>>s), w)
	case "RO":
		s %= uint64(w)
		if w == 64 {
			return bits.RotateLeft64(y, -int(s))
		}
		return uint64(bits.RotateLeft32(uint32(y), -int(s)))
	}
	unmodeled("shift %s", kind)
	return 0
}

func newARM(oa *ops.Arch) *arch {
	arm64 := oa.Name == "ARM64"
	regW := uint8(32)
	if arm64 {
		regW = 64
	}
	a := &arch{name: oa.Name, ptrW: regW, ops: map[string]*opSem{}, blocks: map[string]*blockSem{},
		compute: computeARM(arm64), ccOps: map[string]*cond{}}
	for _, name := range []string{"EQ", "NE", "HS", "LO", "MI", "PL", "VS", "VC", "HI", "LS", "GE", "LT", "GT", "LE"} {
		cat := catInt
		switch name {
		case "EQ", "NE", "MI", "PL", "HS", "LO", "HI", "LS", "GE", "LT", "GT", "LE", "VS", "VC":
			if arm64 {
				cat = catBoth // float conditions use these codes too
			}
		}
		a.conds = append(a.conds, armCond(name, cat))
	}
	has := func(name string) bool { return oa.Op(name) != nil }
	def := func(name string, s *opSem) {
		if has(name) {
			a.ops[name] = s
		}
	}
	cg := parseCodegen(oa)

	// Condition ops (Equal, LessThanU, ...), from codegen's condBits.
	for name, cc := range cg.condBits {
		cd := armCond(cc, category(name))
		if cd == nil || !has(name) {
			continue
		}
		cd.name = name
		a.ccOps[name] = cd
		a.ccOpNames = append(a.ccOpNames, name)
		def(name, &opSem{args: []want{wFlags(cd.cat)}, eval: func(c *ctx, n *node) val {
			return boolVal(test(c, cd, n.args[0].fl))
		}})
	}
	sortStrings(a.ccOpNames)
	ccOf := func(c *ctx, n *node) *cond {
		cd := c.a.ccOps[n.auxOp()]
		if cd == nil {
			unmodeled("condition %s", n.auxOp())
		}
		return cd
	}
	wF := wFlags(catBoth)
	// CSEL [cc] x y f is f satisfies cc ? x : y, and its relatives.
	def("CSEL", &opSem{args: []want{wAny, wAny, wF}, ccArg: 3, eval: func(c *ctx, n *node) val {
		return pick(c, ccOf(c, n), n.args[2].fl, n.args[0], n.args[1])
	}})
	def("FCSELD", a.ops["CSEL"])
	def("FCSELS", a.ops["CSEL"])
	def("CSEL0", &opSem{args: []want{wAny, wF}, ccArg: 2, eval: func(c *ctx, n *node) val {
		return pick(c, ccOf(c, n), n.args[1].fl, n.args[0], intVal(0, 64))
	}})
	csx := func(name string, f func(y uint64) uint64) {
		def(name, &opSem{args: []want{wAny, wInt(64), wF}, ccArg: 3, eval: func(c *ctx, n *node) val {
			return pick(c, ccOf(c, n), n.args[2].fl, n.args[0], intVal(f(n.args[1].i), 64))
		}})
	}
	csx("CSINC", func(y uint64) uint64 { return y + 1 })
	csx("CSINV", func(y uint64) uint64 { return ^y })
	csx("CSNEG", func(y uint64) uint64 { return -y })
	def("CSETM", &opSem{args: []want{wF}, ccArg: 1, eval: func(c *ctx, n *node) val {
		return pick(c, ccOf(c, n), n.args[0].fl, intVal(^uint64(0), 64), intVal(0, 64))
	}})
	// ARM: CMOVWHSconst [c] x f is f satisfies HS ? c : x.
	for _, cc := range []string{"HS", "LS"} {
		cd := armCond(cc, catInt)
		def("CMOVW"+cc+"const", &opSem{args: []want{wAny, wFlags(catInt)}, eval: func(c *ctx, n *node) val {
			return pick(c, cd, n.args[1].fl, intVal(uint64(n.auxInt()), 32), n.args[0])
		}})
	}

	// Flags producers.
	widths := map[string]uint8{"": regW, "W": 32}
	for sfx, w := range widths {
		if sfx == "W" && !arm64 {
			continue
		}
		w := w
		for _, p := range []struct {
			name string
			o    origin
			f    func(x, y uint64) (uint64, uint64)
		}{
			{"CMP", oSub, func(x, y uint64) (uint64, uint64) { return x, y }},
			{"CMN", oAdd, func(x, y uint64) (uint64, uint64) { return x, y }},
			{"TST", oLogic, func(x, y uint64) (uint64, uint64) { return x & y, 0 }},
			{"TEQ", oLogic, func(x, y uint64) (uint64, uint64) { return x ^ y, 0 }},
		} {
			p := p
			def(p.name+sfx, &opSem{args: wInts(2, w), origin: p.o, eval: func(c *ctx, n *node) val {
				x, y := p.f(n.args[0].i, n.args[1].i)
				return flagsVal(c.a.newFlags(n.op, p.o, x, y, w))
			}})
			def(p.name+sfx+"const", &opSem{args: wInts(1, w), origin: p.o, eval: func(c *ctx, n *node) val {
				x, y := p.f(n.args[0].i, uint64(n.auxInt()))
				return flagsVal(c.a.newFlags(n.op, p.o, x, y, w))
			}})
			for _, k := range []string{"LL", "RL", "RA", "RO"} {
				k := k
				// CMPshiftLL x y [c] compares x with y<<c.
				def(p.name+sfx+"shift"+k, &opSem{args: wInts(2, w), origin: p.o, auxRange: rng(0, int64(w)-1), eval: func(c *ctx, n *node) val {
					x, y := p.f(n.args[0].i, armShift(k, n.args[1].i, uint64(n.auxInt()), w))
					return flagsVal(c.a.newFlags(n.op, p.o, x, y, w))
				}})
				// ARM: CMPshiftLLreg x y z compares x with y<<z.
				def(p.name+sfx+"shift"+k+"reg", &opSem{args: wInts(3, w), origin: p.o, eval: func(c *ctx, n *node) val {
					x, y := p.f(n.args[0].i, armShift(k, n.args[1].i, n.args[2].i&0xff, w))
					return flagsVal(c.a.newFlags(n.op, p.o, x, y, w))
				}})
			}
		}
	}
	for _, f := range []struct {
		name string
		w    uint8
		zero bool
	}{{"FCMPS", 32, false}, {"FCMPD", 64, false}, {"FCMPS0", 32, true}, {"FCMPD0", 64, true},
		{"CMPF", 32, false}, {"CMPD", 64, false}, {"CMPF0", 32, true}, {"CMPD0", 64, true}} {
		f := f
		nargs := 2
		if f.zero {
			nargs = 1
		}
		args := []want{wFloat(f.w), wFloat(f.w)}[:nargs]
		def(f.name, &opSem{args: args, origin: oFloat, eval: func(c *ctx, n *node) val {
			y := 0.0
			if !f.zero {
				y = n.args[1].f
			}
			return flagsVal(c.a.newFloatFlags(n.op, n.args[0].f, y))
		}})
	}
	if has("FlagConstant") {
		for fc := range uint64(16) {
			a.consts = append(a.consts, flagConstant(fc))
		}
	}
	def("FlagConstant", &opSem{origin: oConst, eval: func(c *ctx, n *node) val {
		return flagsVal(flagConstant(uint64(n.auxInt())))
	}})
	def("InvertFlags", &opSem{args: []want{wFlagsInv()}, inherit: true, eval: func(c *ctx, n *node) val {
		return flagsVal(c.a.invert(n.args[0].fl))
	}})

	// Integer ops.
	mov := "MOVD"
	if !arm64 {
		mov = "MOVW"
	}
	def(mov+"const", &opSem{eval: func(c *ctx, n *node) val { return intVal(uint64(n.auxInt()), regW) }})
	alu := func(name string, f func(x, y uint64) uint64) {
		def(name, &opSem{args: wInts(2, regW), eval: func(c *ctx, n *node) val {
			return intVal(f(n.args[0].i, n.args[1].i), regW)
		}})
		def(name+"const", &opSem{args: wInts(1, regW), eval: func(c *ctx, n *node) val {
			return intVal(f(n.args[0].i, uint64(n.auxInt())), regW)
		}})
		for _, k := range []string{"LL", "RL", "RA"} {
			k := k
			def(name+"shift"+k, &opSem{args: wInts(2, regW), auxRange: rng(0, int64(regW)-1), eval: func(c *ctx, n *node) val {
				return intVal(f(n.args[0].i, armShift(k, n.args[1].i, uint64(n.auxInt()), regW)), regW)
			}})
			def(name+"shift"+k+"reg", &opSem{args: wInts(3, regW), eval: func(c *ctx, n *node) val {
				return intVal(f(n.args[0].i, armShift(k, n.args[1].i, n.args[2].i&0xff, regW)), regW)
			}})
		}
	}
	alu("ADD", func(x, y uint64) uint64 { return x + y })
	alu("SUB", func(x, y uint64) uint64 { return x - y })
	alu("RSB", func(x, y uint64) uint64 { return y - x })
	alu("AND", func(x, y uint64) uint64 { return x & y })
	alu("OR", func(x, y uint64) uint64 { return x | y })
	alu("XOR", func(x, y uint64) uint64 { return x ^ y })
	alu("BIC", func(x, y uint64) uint64 { return x &^ y })
	alu("MUL", func(x, y uint64) uint64 { return x * y })
	def("NEG", &opSem{args: wInts(1, regW), eval: func(c *ctx, n *node) val { return intVal(-n.args[0].i, regW) }})
	def("MVN", &opSem{args: wInts(1, regW), eval: func(c *ctx, n *node) val { return intVal(^n.args[0].i, regW) }})
	def("MULW", &opSem{args: wInts(2, 32), eval: func(c *ctx, n *node) val {
		return intVal(trunc(n.args[0].i*n.args[1].i, 32), regW)
	}})
	if arm64 {
		// MADD a x y is a + x*y; MSUB a x y is a - x*y.
		def("MADD", &opSem{args: wInts(3, 64), eval: func(c *ctx, n *node) val {
			return intVal(n.args[0].i+n.args[1].i*n.args[2].i, 64)
		}})
		def("MSUB", &opSem{args: wInts(3, 64), eval: func(c *ctx, n *node) val {
			return intVal(n.args[0].i-n.args[1].i*n.args[2].i, 64)
		}})
		def("MADDW", &opSem{args: wInts(3, 32), eval: func(c *ctx, n *node) val {
			return intVal(trunc(n.args[0].i+n.args[1].i*n.args[2].i, 32), 64)
		}})
		def("MSUBW", &opSem{args: wInts(3, 32), eval: func(c *ctx, n *node) val {
			return intVal(trunc(n.args[0].i-n.args[1].i*n.args[2].i, 32), 64)
		}})
	} else {
		// MULA x y a is x*y + a; MULS x y a is a - x*y.
		def("MULA", &opSem{args: wInts(3, 32), eval: func(c *ctx, n *node) val {
			return intVal(n.args[0].i*n.args[1].i+n.args[2].i, 32)
		}})
		def("MULS", &opSem{args: wInts(3, 32), eval: func(c *ctx, n *node) val {
			return intVal(n.args[2].i-n.args[0].i*n.args[1].i, 32)
		}})
	}
	if !arm64 {
		// Register shifts take the amount mod 256 (ARMOps.go).
		for _, k := range []string{"LL", "RL", "RA"} {
			k := k
			name := map[string]string{"LL": "SLL", "RL": "SRL", "RA": "SRA"}[k]
			def(name, &opSem{args: wInts(2, 32), eval: func(c *ctx, n *node) val {
				return intVal(armShift(k, n.args[0].i, n.args[1].i&0xff, 32), 32)
			}})
		}
	}
	if arm64 {
		// Register shifts take the amount mod 64 (ARM64Ops.go).
		for _, k := range []string{"LL", "RL", "RA"} {
			k := k
			name := map[string]string{"LL": "SLL", "RL": "SRL", "RA": "SRA"}[k]
			def(name, &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val {
				return intVal(armShift(k, n.args[0].i, n.args[1].i&63, 64), 64)
			}})
		}
	}
	// Shift amounts are in [0, regW) (ARM64Ops.go, ARMOps.go).
	for _, k := range []string{"LL", "RL", "RA", "RO"} {
		k := k
		name := map[string]string{"LL": "SLL", "RL": "SRL", "RA": "SRA", "RO": "ROR"}[k]
		def(name+"const", &opSem{args: wInts(1, regW), auxRange: rng(0, int64(regW)-1), eval: func(c *ctx, n *node) val {
			return intVal(armShift(k, n.args[0].i, uint64(n.auxInt()), regW), regW)
		}})
	}
	for _, e := range []struct {
		name   string
		w      uint8
		signed bool
	}{{"MOVBUreg", 8, false}, {"MOVHUreg", 16, false}, {"MOVWUreg", 32, false},
		{"MOVBreg", 8, true}, {"MOVHreg", 16, true}, {"MOVWreg", 32, true}} {
		e := e
		if e.w >= regW {
			continue
		}
		def(e.name, &opSem{args: wInts(1, e.w), eval: func(c *ctx, n *node) val {
			if e.signed {
				return intVal(uint64(sext(n.args[0].i, e.w)), regW)
			}
			return intVal(trunc(n.args[0].i, e.w), regW)
		}})
	}

	// Blocks, from codegen's blockJump.
	for blk, cc := range cg.blockJump {
		if oa.Block(blk) == nil {
			continue
		}
		switch blk {
		case "Z", "NZ", "ZW", "NZW", "TBZ", "TBNZ":
			continue
		}
		if cd := armCond(cc, category(blk)); cd != nil {
			defBlock(a, blk, cd, cd.cat)
		}
	}
	for blk, test := range map[string]string{"LEnoov": "EQ||MI", "GTnoov": "!EQ&&!MI"} {
		if oa.Block(blk) != nil {
			cd := armCond(blk, catInt)
			cd.name = test
			defBlock(a, blk, cd, catInt)
		}
	}
	zb := func(name string, w uint8, zero bool) {
		if oa.Block(name) == nil {
			return
		}
		a.blocks[name] = &blockSem{controls: []want{wInt(w)}, eval: func(c *ctx, n *node) bool {
			return (trunc(n.args[0].i, w) == 0) == zero
		}}
	}
	zb("Z", 64, true)
	zb("NZ", 64, false)
	zb("ZW", 32, true)
	zb("NZW", 32, false)
	for _, name := range []string{"TBZ", "TBNZ"} {
		zero := name == "TBZ"
		if oa.Block(name) == nil {
			continue
		}
		a.blocks[name] = &blockSem{controls: []want{wInt(64)}, eval: func(c *ctx, n *node) bool {
			k := n.auxInt()
			if k < 0 || k > 63 {
				impossible()
			}
			return (n.args[0].i>>k&1 == 0) == zero
		}}
	}

	a.producers = []producer{{op: "CMP", o: oSub, w: regW}, {op: "CMN", o: oAdd, w: regW}, {op: "TST", o: oLogic, w: regW}}
	if arm64 {
		a.producers = append(a.producers, producer{op: "CMPW", o: oSub, w: 32}, producer{op: "CMNW", o: oAdd, w: 32}, producer{op: "TSTW", o: oLogic, w: 32},
			producer{op: "FCMPD", o: oFloat, w: 64})
	} else {
		a.producers = append(a.producers, producer{op: "CMPD", o: oFloat, w: 64})
	}
	return a
}

// arm64Negate and arm64Invert are the helpers of the same names in the
// ARM64 rewrite package (arm64_helpers.go): the condition's complement,
// and the condition with its operands swapped.
var arm64Negate = map[string]string{
	"LessThan": "GreaterEqual", "LessThanU": "GreaterEqualU", "GreaterThan": "LessEqual", "GreaterThanU": "LessEqualU",
	"LessEqual": "GreaterThan", "LessEqualU": "GreaterThanU", "GreaterEqual": "LessThan", "GreaterEqualU": "LessThanU",
	"Equal": "NotEqual", "NotEqual": "Equal",
	"LessThanF": "NotLessThanF", "NotLessThanF": "LessThanF", "LessEqualF": "NotLessEqualF", "NotLessEqualF": "LessEqualF",
	"GreaterThanF": "NotGreaterThanF", "NotGreaterThanF": "GreaterThanF", "GreaterEqualF": "NotGreaterEqualF", "NotGreaterEqualF": "GreaterEqualF",
}

var arm64Invert = map[string]string{
	"LessThan": "GreaterThan", "LessThanU": "GreaterThanU", "GreaterThan": "LessThan", "GreaterThanU": "LessThanU",
	"LessEqual": "GreaterEqual", "LessEqualU": "GreaterEqualU", "GreaterEqual": "LessEqual", "GreaterEqualU": "LessEqualU",
	"Equal": "Equal", "NotEqual": "NotEqual",
	"LessThanF": "GreaterThanF", "GreaterThanF": "LessThanF", "LessEqualF": "GreaterEqualF", "GreaterEqualF": "LessEqualF",
	"NotLessThanF": "NotGreaterThanF", "NotGreaterThanF": "NotLessThanF", "NotLessEqualF": "NotGreaterEqualF", "NotGreaterEqualF": "NotLessEqualF",
}

// ccARM64EvalOps are the conditions ccARM64Eval evaluates.
var ccARM64EvalOps = map[string]bool{
	"Equal": true, "NotEqual": true, "LessThan": true, "LessThanU": true, "GreaterThan": true,
	"GreaterThanU": true, "LessEqual": true, "LessEqualU": true, "GreaterEqual": true, "GreaterEqualU": true,
}

// ccARM64Eval mirrors the ARM64 rewrite helper of the same name: 1 if
// condition op holds for constant flags, -1 if not, 0 if the flags
// aren't constant. It negates (rather than swaps) through InvertFlags,
// as the helper does.
func (c *ctx) ccARM64Eval(op, fv gv) int {
	if op.k != gOp || fv.k != gValue || fv.v.k != kFlags {
		unmodeled("ccARM64Eval(%v, %v)", op, fv)
	}
	var eval func(f *flags) int
	eval = func(f *flags) int {
		if f.op == "InvertFlags" {
			return -eval(f.inner)
		}
		if f.op != "FlagConstant" {
			return 0
		}
		cd := c.a.ccOps[op.s]
		if cd == nil || !ccARM64EvalOps[op.s] {
			return 0
		}
		if cd.eval(f) == tTrue {
			return 1
		}
		return -1
	}
	return eval(fv.v.fl)
}
