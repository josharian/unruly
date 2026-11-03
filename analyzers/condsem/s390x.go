package condsem

import (
	"go/types"

	"github.com/josharian/unruly/ops"
)

// S390X has a two-bit condition code (CC). Compares set CC 0 for equal,
// 1 for less, 2 for greater, and 3 for unordered (float). Consumers test
// it against a mask (s390x.CCMask, cmd/internal/obj/s390x): bit 8>>CC set
// means the condition holds. The CC is modeled with the bits EQ, LT, GT,
// and SO (for CC 3).
var s390xCC = [4]bit{bEQ, bLT, bGT, bSO}

func computeS390X(f *flags) {
	switch f.o {
	case oSub:
		x, y := trunc(f.a, f.w), trunc(f.b, f.w)
		var c int
		if f.signed {
			c = compareInt(sext(x, f.w), sext(y, f.w))
		} else {
			c = compareUint(x, y)
		}
		setCC(f, map[int]int{0: 0, -1: 1, 1: 2}[c])
	case oFloat:
		x, y := f.fa, f.fb
		switch {
		case x != x || y != y:
			setCC(f, 3)
		case x == y:
			setCC(f, 0)
		case x < y:
			setCC(f, 1)
		default:
			setCC(f, 2)
		}
	}
}

func setCC(f *flags, cc int) {
	for i, b := range s390xCC {
		f.setBit(b, i == cc)
	}
}

// ccMask returns the condition that mask m (an s390x.CCMask) tests.
func ccMask(m uint64) *cond {
	return &cond{name: "mask", cat: catBoth, eval: func(f *flags) tri {
		t := tFalse
		for i, b := range s390xCC {
			if m&(8>>i) != 0 {
				t = t.or(f.get(b))
			}
		}
		return t
	}}
}

func newS390X(oa *ops.Arch) *arch {
	a := &arch{name: oa.Name, ptrW: 64, ops: map[string]*opSem{}, blocks: map[string]*blockSem{}, compute: computeS390X}
	for m := uint64(1); m < 16; m <<= 1 {
		cd := ccMask(m)
		cd.name = []string{"", "CC3 (unordered)", "CC2 (greater)", "", "CC1 (less)", "", "", "", "CC0 (equal)"}[m]
		a.conds = append(a.conds, cd)
	}
	has := func(name string) bool { return oa.Op(name) != nil }
	def := func(name string, s *opSem) {
		if has(name) {
			a.ops[name] = s
		}
	}
	maskOf := func(n *node) *cond {
		if n.aux.k != gInt {
			unmodeled("%s aux %v", n.op, n.aux)
		}
		return ccMask(n.aux.i)
	}
	// LOCGR {c} x y f is f matches c ? y : x (S390XOps.go).
	def("LOCGR", &opSem{args: []want{wAny, wAny, wFlags(catBoth)}, eval: func(c *ctx, n *node) val {
		return pick(c, maskOf(n), n.args[2].fl, n.args[1], n.args[0])
	}})

	// Compares. The unsigned compares with an immediate zero-extend it
	// (s390x/ssa.go: int64(uint32(v.AuxInt))).
	mk := func(c *ctx, n *node, x, y uint64, w uint8, signed bool) *flags {
		f := &flags{op: n.op, o: oSub, a: trunc(x, w), b: trunc(y, w), w: w, signed: signed}
		c.a.compute(f)
		return f
	}
	for _, p := range []struct {
		name   string
		w      uint8
		signed bool
	}{{"CMP", 64, true}, {"CMPU", 64, false}, {"CMPW", 32, true}, {"CMPWU", 32, false}} {
		p := p
		def(p.name, &opSem{args: wInts(2, p.w), origin: oSub, eval: func(c *ctx, n *node) val {
			return flagsVal(mk(c, n, n.args[0].i, n.args[1].i, p.w, p.signed))
		}})
		def(p.name+"const", &opSem{args: wInts(1, p.w), origin: oSub, eval: func(c *ctx, n *node) val {
			imm := uint64(n.auxInt())
			if !p.signed {
				imm = uint64(uint32(imm))
			}
			return flagsVal(mk(c, n, n.args[0].i, imm, p.w, p.signed))
		}})
		a.producers = append(a.producers, producer{op: p.name, o: oSub, w: p.w, signed: p.signed})
	}
	for _, name := range []string{"FCMP", "FCMPS"} {
		w := uint8(64)
		if name == "FCMPS" {
			w = 32
		}
		def(name, &opSem{args: []want{wFloat(w), wFloat(w)}, origin: oFloat, eval: func(c *ctx, n *node) val {
			return flagsVal(c.a.newFloatFlags(n.op, n.args[0].f, n.args[1].f))
		}})
	}
	a.producers = append(a.producers, producer{op: "FCMP", o: oFloat})
	for i, k := range []string{"FlagEQ", "FlagLT", "FlagGT", "FlagOV"} {
		f := &flags{op: k, o: oConst}
		setCC(f, i)
		if has(k) {
			a.consts = append(a.consts, f)
		}
		def(k, &opSem{origin: oConst, eval: func(c *ctx, n *node) val { return flagsVal(f) }})
	}
	def("InvertFlags", &opSem{args: []want{wFlagsInv()}, inherit: true, eval: func(c *ctx, n *node) val {
		return flagsVal(c.a.invert(n.args[0].fl))
	}})

	// Integer ops.
	def("MOVDconst", &opSem{eval: func(c *ctx, n *node) val { return intVal(uint64(n.auxInt()), 64) }})
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
	def("NEG", &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val { return intVal(-n.args[0].i, 64) }})
	def("ANDWconst", &opSem{args: wInts(1, 32), eval: func(c *ctx, n *node) val {
		return intVal(trunc(n.args[0].i&uint64(n.auxInt()), 32), 32)
	}})
	// Shifts: amounts are mod 64 (S390XOps.go), so a 32-bit shift by
	// 32 to 63 shifts everything out.
	for _, s := range []struct {
		name string
		k    string
		w    uint8
	}{{"SLD", "LL", 64}, {"SRD", "RL", 64}, {"SRAD", "RA", 64}, {"SLW", "LL", 32}, {"SRW", "RL", 32}, {"SRAW", "RA", 32}} {
		s := s
		ext := func(x uint64) val {
			if s.k == "RA" {
				return intVal(uint64(sext(x, s.w)), 64)
			}
			return intVal(x, 64)
		}
		def(s.name, &opSem{args: []want{wInt(s.w), wInt(64)}, eval: func(c *ctx, n *node) val {
			return ext(armShift(s.k, n.args[0].i, n.args[1].i&63, s.w))
		}})
		def(s.name+"const", &opSem{args: []want{wInt(s.w)}, auxRange: rng(0, int64(s.w)-1), eval: func(c *ctx, n *node) val {
			return ext(armShift(s.k, n.args[0].i, uint64(n.auxInt()), s.w))
		}})
	}

	// Blocks. BRC {c} f branches on f matching c. The compare-and-branch
	// blocks compare their controls (or a control and the auxint, which
	// is int8 for the signed forms and uint8 for the unsigned) and branch
	// on the result matching c.
	a.blocks["BRC"] = &blockSem{controls: []want{wFlags(catBoth)}, eval: func(c *ctx, n *node) bool {
		return test(c, maskOf(n), n.args[0].fl)
	}}
	for _, b := range []struct {
		name   string
		w      uint8
		signed bool
		imm    bool
	}{{"CRJ", 32, true, false}, {"CGRJ", 64, true, false}, {"CLRJ", 32, false, false}, {"CLGRJ", 64, false, false},
		{"CIJ", 32, true, true}, {"CGIJ", 64, true, true}, {"CLIJ", 32, false, true}, {"CLGIJ", 64, false, true}} {
		b := b
		if oa.Block(b.name) == nil {
			continue
		}
		ctl := wInts(2, b.w)
		if b.imm {
			ctl = ctl[:1]
		}
		a.blocks[b.name] = &blockSem{controls: ctl, eval: func(c *ctx, n *node) bool {
			var y uint64
			if b.imm {
				y = uint64(n.auxInt()) // already sign- or zero-extended per its Go type
			} else {
				y = n.args[1].i
			}
			return test(c, maskOf(n), mk(c, n, n.args[0].i, y, b.w, b.signed))
		}}
	}
	return a
}

// ccMaskMethod evaluates a method of s390x.CCMask.
func ccMaskMethod(name string, recv gv) gv {
	n, ok := recv.t.(*types.Named)
	if !ok || n.Obj().Name() != "CCMask" {
		return top
	}
	m := recv.i
	switch name {
	case "inverse":
		return gv{k: gInt, i: m ^ 15, t: recv.t}
	case "reverseComparison":
		// cmd/internal/obj/s390x: swap Less and Greater.
		r := m & (8 | 1)
		if m&4 != 0 {
			r |= 2
		}
		if m&2 != 0 {
			r |= 4
		}
		return gv{k: gInt, i: r, t: recv.t}
	}
	unmodeled("CCMask.%s", name)
	return top
}
