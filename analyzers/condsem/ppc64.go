package condsem

import (
	"github.com/josharian/unruly/ops"
)

// PPC64 compares set one condition register field: LT, GT, EQ, and SO,
// which is the unordered bit after FCMPU and otherwise a copy of the
// summary overflow bit, which nothing models.
func computePPC64(f *flags) {
	switch f.o {
	case oSub:
		x, y := trunc(f.a, f.w), trunc(f.b, f.w)
		var c int
		if f.signed {
			c = compareInt(sext(x, f.w), sext(y, f.w))
		} else {
			c = compareUint(x, y)
		}
		f.setBit(bLT, c < 0)
		f.setBit(bGT, c > 0)
		f.setBit(bEQ, c == 0)
		f.markStale(bSO)
	case oLogic:
		// Record forms (ANDCC, ...) compare the 64-bit result with 0.
		r := int64(f.a)
		f.setBit(bLT, r < 0)
		f.setBit(bGT, r > 0)
		f.setBit(bEQ, r == 0)
		f.markStale(bSO)
	case oFloat:
		x, y := f.fa, f.fb
		un := x != x || y != y
		f.setBit(bLT, !un && x < y)
		f.setBit(bGT, !un && x > y)
		f.setBit(bEQ, !un && x == y)
		f.setBit(bSO, un)
	}
}

var ppcBits = [4]bit{bLT, bGT, bEQ, bSO}

// ppcConds are the PPC64 branch conditions (BEQ, BNE, BLT, BGE, BLE,
// BGT, BVS): BGE and BLE are "not LT" and "not GT".
var ppcConds = map[string]func(f *flags) tri{
	"EQ": func(f *flags) tri { return f.get(bEQ) },
	"NE": func(f *flags) tri { return f.get(bEQ).not() },
	"LT": func(f *flags) tri { return f.get(bLT) },
	"GE": func(f *flags) tri { return f.get(bLT).not() },
	"GT": func(f *flags) tri { return f.get(bGT) },
	"LE": func(f *flags) tri { return f.get(bGT).not() },
	"VS": func(f *flags) tri { return f.get(bSO) },
	"VC": func(f *flags) tri { return f.get(bSO).not() },
}

// ppcPseudo are the PPC64 condition pseudo-ops (PPC64Ops.go), which
// lowering turns into SETBC and SETBCR (PPC64.rules): LessEqual is
// SETBCR [1] (not GT), FLessEqual is LT or EQ.
var ppcPseudo = map[string]func(f *flags) tri{
	"Equal":         ppcConds["EQ"],
	"NotEqual":      ppcConds["NE"],
	"LessThan":      ppcConds["LT"],
	"LessEqual":     ppcConds["LE"],
	"GreaterThan":   ppcConds["GT"],
	"GreaterEqual":  ppcConds["GE"],
	"FLessThan":     ppcConds["LT"],
	"FGreaterThan":  ppcConds["GT"],
	"FLessEqual":    func(f *flags) tri { return f.get(bLT).or(f.get(bEQ)) },
	"FGreaterEqual": func(f *flags) tri { return f.get(bGT).or(f.get(bEQ)) },
}

func newPPC64(oa *ops.Arch) *arch {
	a := &arch{name: oa.Name, ptrW: 64, ops: map[string]*opSem{}, blocks: map[string]*blockSem{}, compute: computePPC64}
	for _, name := range []string{"EQ", "LT", "GT", "VS"} {
		a.conds = append(a.conds, &cond{name: name, cat: catBoth, eval: ppcConds[name]})
	}
	has := func(name string) bool { return oa.Op(name) != nil }
	def := func(name string, s *opSem) {
		if has(name) {
			a.ops[name] = s
		}
	}
	for name, f := range ppcPseudo {
		cd := &cond{name: name, cat: category(name), eval: f}
		def(name, &opSem{args: []want{wFlags(cd.cat)}, eval: func(c *ctx, n *node) val {
			return boolVal(test(c, cd, n.args[0].fl))
		}})
	}
	// ppc64/ssa.go: ISEL [a] x y f is (the CR bit a&3 of f) ? x : y for
	// a < 4, and the same with x and y swapped for a > 3. SETBC [a] f is
	// CR0 bit a.
	bitCond := func(c *ctx, n *node, maxAux int64) (*cond, bool) {
		k := n.auxInt()
		if k < 0 || k > maxAux {
			c.badAux(n, k)
		}
		b := ppcBits[k&3]
		return &cond{name: bitNames[b], cat: catBoth, eval: func(f *flags) tri { return f.get(b) }}, k > 3
	}
	def("ISEL", &opSem{args: []want{wAny, wAny, wFlags(catBoth)}, eval: func(c *ctx, n *node) val {
		cd, swap := bitCond(c, n, 7)
		x, y := n.args[0], n.args[1]
		if swap {
			x, y = y, x
		}
		return pick(c, cd, n.args[2].fl, x, y)
	}})
	def("ISELZ", &opSem{args: []want{wAny, wFlags(catBoth)}, eval: func(c *ctx, n *node) val {
		cd, swap := bitCond(c, n, 7)
		x, y := n.args[0], intVal(0, 64)
		if swap {
			x, y = y, x
		}
		return pick(c, cd, n.args[1].fl, x, y)
	}})
	for _, name := range []string{"SETBC", "SETBCR"} {
		rev := name == "SETBCR"
		def(name, &opSem{args: []want{wFlags(catBoth)}, eval: func(c *ctx, n *node) val {
			cd, _ := bitCond(c, n, 3)
			return boolVal(test(c, cd, n.args[0].fl) != rev)
		}})
	}

	// Producers.
	for _, p := range []struct {
		name   string
		w      uint8
		signed bool
	}{{"CMP", 64, true}, {"CMPU", 64, false}, {"CMPW", 32, true}, {"CMPWU", 32, false}} {
		p := p
		mk := func(c *ctx, n *node, x, y uint64) val {
			f := &flags{op: n.op, o: oSub, a: trunc(x, p.w), b: trunc(y, p.w), w: p.w, signed: p.signed}
			c.a.compute(f)
			return flagsVal(f)
		}
		def(p.name, &opSem{args: wInts(2, p.w), origin: oSub, eval: func(c *ctx, n *node) val {
			return mk(c, n, n.args[0].i, n.args[1].i)
		}})
		def(p.name+"const", &opSem{args: wInts(1, p.w), origin: oSub, eval: func(c *ctx, n *node) val {
			return mk(c, n, n.args[0].i, uint64(n.auxInt()))
		}})
		a.producers = append(a.producers, producer{op: p.name, o: oSub, w: p.w, signed: p.signed})
	}
	def("FCMPU", &opSem{args: []want{wFloat(64), wFloat(64)}, origin: oFloat, eval: func(c *ctx, n *node) val {
		return flagsVal(c.a.newFloatFlags(n.op, n.args[0].f, n.args[1].f))
	}})
	a.producers = append(a.producers, producer{op: "FCMPU", o: oFloat})
	for _, k := range []string{"EQ", "LT", "GT"} {
		b := map[string]bit{"EQ": bEQ, "LT": bLT, "GT": bGT}[k]
		f := &flags{op: "Flag" + k, o: oConst}
		for _, x := range []bit{bLT, bGT, bEQ} {
			f.setBit(x, x == b)
		}
		f.markStale(bSO)
		if has(f.op) {
			a.consts = append(a.consts, f)
		}
		def(f.op, &opSem{origin: oConst, eval: func(c *ctx, n *node) val { return flagsVal(f) }})
	}
	def("InvertFlags", &opSem{args: []want{wFlagsInv()}, inherit: true, eval: func(c *ctx, n *node) val {
		return flagsVal(c.a.invert(n.args[0].fl))
	}})
	// Record forms produce (result, flags of result vs 0).
	rec := func(name string, nargs int, f func(n *node) uint64) {
		def(name, &opSem{args: wInts(nargs, 64), eval: func(c *ctx, n *node) val {
			r := f(n)
			return val{k: kTuple, xs: []val{intVal(r, 64), flagsVal(c.a.newFlags(n.op, oLogic, r, 0, 64))}}
		}})
	}
	rec("ANDCC", 2, func(n *node) uint64 { return n.args[0].i & n.args[1].i })
	rec("ORCC", 2, func(n *node) uint64 { return n.args[0].i | n.args[1].i })
	rec("XORCC", 2, func(n *node) uint64 { return n.args[0].i ^ n.args[1].i })
	rec("ANDCCconst", 1, func(n *node) uint64 { return n.args[0].i & uint64(n.auxInt()) })

	// Integer ops.
	def("MOVDconst", &opSem{eval: func(c *ctx, n *node) val { return intVal(uint64(n.auxInt()), 64) }})
	alu := func(name string, f func(x, y uint64) uint64) {
		def(name, &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val {
			return intVal(f(n.args[0].i, n.args[1].i), 64)
		}})
		def(name+"const", &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val {
			return intVal(f(n.args[0].i, uint64(n.auxInt())), 64)
		}})
	}
	alu("ADD", func(x, y uint64) uint64 { return x + y })
	alu("AND", func(x, y uint64) uint64 { return x & y })
	alu("OR", func(x, y uint64) uint64 { return x | y })
	alu("XOR", func(x, y uint64) uint64 { return x ^ y })
	// Every rule that creates an ANDconst (or, in late lowering, an
	// ANDCCconst) limits its constant to 16 unsigned bits (isU16Bit, or
	// masks of such constants), so other constants don't occur.
	for _, name := range []string{"ANDconst", "ANDCCconst"} {
		if s := a.ops[name]; s != nil {
			s.auxRange = rng(0, 0xffff)
		}
	}
	def("SUB", &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val { return intVal(n.args[0].i-n.args[1].i, 64) }})
	def("NEG", &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val { return intVal(-n.args[0].i, 64) }})
	for _, e := range []struct {
		name   string
		w      uint8
		signed bool
	}{{"MOVBZreg", 8, false}, {"MOVHZreg", 16, false}, {"MOVWZreg", 32, false},
		{"MOVBreg", 8, true}, {"MOVHreg", 16, true}, {"MOVWreg", 32, true}} {
		e := e
		def(e.name, &opSem{args: wInts(1, e.w), eval: func(c *ctx, n *node) val {
			if e.signed {
				return intVal(uint64(sext(n.args[0].i, e.w)), 64)
			}
			return intVal(trunc(n.args[0].i, e.w), 64)
		}})
	}

	// Shifts (PPC64Ops.go): 64-bit shifts take the amount mod 128 and
	// 32-bit shifts mod 64, shifting everything out past the width.
	for _, s := range []struct {
		name string
		k    string
		w    uint8
		mask uint64
	}{{"SLD", "LL", 64, 127}, {"SRD", "RL", 64, 127}, {"SRAD", "RA", 64, 127}, {"SLW", "LL", 32, 63}, {"SRW", "RL", 32, 63}, {"SRAW", "RA", 32, 63}} {
		s := s
		ext := func(x uint64) val {
			if s.k == "RA" {
				return intVal(uint64(sext(x, s.w)), 64)
			}
			return intVal(x, 64)
		}
		def(s.name, &opSem{args: []want{wInt(s.w), wInt(64)}, eval: func(c *ctx, n *node) val {
			return ext(armShift(s.k, n.args[0].i, n.args[1].i&s.mask, s.w))
		}})
		def(s.name+"const", &opSem{args: []want{wInt(s.w)}, auxRange: rng(0, int64(s.w)-1), eval: func(c *ctx, n *node) val {
			return ext(armShift(s.k, n.args[0].i, uint64(n.auxInt()), s.w))
		}})
	}

	// Blocks, from codegen's blockJump; asmeq adds a branch on EQ.
	cg := parseCodegen(oa)
	for blk, cc := range cg.blockJump {
		f := ppcConds[cc]
		if f == nil || oa.Block(blk) == nil {
			continue
		}
		eval := f
		if cg.blockEq[blk] {
			eval = func(fl *flags) tri { return f(fl).or(fl.get(bEQ)) }
		}
		defBlock(a, blk, &cond{name: blk, eval: eval}, category(blk))
	}
	return a
}
