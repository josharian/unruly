package condsem

import (
	"fmt"
	"math/bits"
)

// genericOps are the semantics of the generic ops that flags-related
// rules match (mostly comparisons being lowered). Integer arguments are
// 64-bit patterns whose low bits are meaningful; booleans are 0 or 1.
var genericOps = map[string]*opSem{}

// genericBlocks are the semantics of generic block kinds.
var genericBlocks = map[string]*blockSem{
	"If": {controls: []want{wBool}, eval: func(c *ctx, n *node) bool { return n.args[0].i&0xff != 0 }},
}

func init() {
	for _, w := range []uint8{8, 16, 32, 64} {
		w := w
		sfx := fmt.Sprint(w)
		genericOps["Const"+sfx] = &opSem{eval: func(c *ctx, n *node) val { return intVal(uint64(n.auxInt()), w) }}
		cmp := func(name string, f func(x, y uint64) bool) {
			genericOps[name] = &opSem{args: wInts(2, w), eval: func(c *ctx, n *node) val {
				return boolVal(f(trunc(n.args[0].i, w), trunc(n.args[1].i, w)))
			}}
		}
		cmp("Eq"+sfx, func(x, y uint64) bool { return x == y })
		cmp("Neq"+sfx, func(x, y uint64) bool { return x != y })
		cmp("Less"+sfx, func(x, y uint64) bool { return sext(x, w) < sext(y, w) })
		cmp("Leq"+sfx, func(x, y uint64) bool { return sext(x, w) <= sext(y, w) })
		cmp("Less"+sfx+"U", func(x, y uint64) bool { return x < y })
		cmp("Leq"+sfx+"U", func(x, y uint64) bool { return x <= y })
		for _, to := range []uint8{16, 32, 64} {
			if to <= w {
				continue
			}
			from, to := w, to
			genericOps[fmt.Sprintf("SignExt%dto%d", from, to)] = &opSem{args: []want{wInt(from)}, eval: func(c *ctx, n *node) val {
				return intVal(uint64(sext(n.args[0].i, from)), to)
			}}
			genericOps[fmt.Sprintf("ZeroExt%dto%d", from, to)] = &opSem{args: []want{wInt(from)}, eval: func(c *ctx, n *node) val {
				return intVal(trunc(n.args[0].i, from), to)
			}}
			genericOps[fmt.Sprintf("Trunc%dto%d", to, from)] = &opSem{args: []want{wInt(to)}, eval: func(c *ctx, n *node) val {
				return intVal(n.args[0].i, from)
			}}
		}
	}
	for _, w := range []uint8{32, 64} {
		w := w
		sfx := fmt.Sprint(w)
		genericOps["Const"+sfx+"F"] = &opSem{eval: func(c *ctx, n *node) val {
			if n.auxint.k != gFloat {
				unmodeled("float constant %v", n.auxint)
			}
			return floatVal(n.auxint.f, w)
		}}
		fcmp := func(name string, f func(x, y float64) bool) {
			genericOps[name] = &opSem{args: []want{wFloat(w), wFloat(w)}, eval: func(c *ctx, n *node) val {
				return boolVal(f(n.args[0].f, n.args[1].f))
			}}
		}
		fcmp("Eq"+sfx+"F", func(x, y float64) bool { return x == y })
		fcmp("Neq"+sfx+"F", func(x, y float64) bool { return x != y })
		fcmp("Less"+sfx+"F", func(x, y float64) bool { return x < y })
		fcmp("Leq"+sfx+"F", func(x, y float64) bool { return x <= y })
	}
	genericOps["ConstBool"] = &opSem{eval: func(c *ctx, n *node) val {
		switch n.auxint.k {
		case gBool:
			return boolVal(n.auxint.b)
		case gInt:
			return boolVal(n.auxint.i != 0)
		}
		unmodeled("ConstBool %v", n.auxint)
		return val{}
	}}
	genericOps["Not"] = &opSem{args: []want{wBool}, eval: func(c *ctx, n *node) val { return boolVal(n.args[0].i&1 == 0) }}
	genericOps["EqB"] = &opSem{args: []want{wBool, wBool}, eval: func(c *ctx, n *node) val { return boolVal(n.args[0].i&1 == n.args[1].i&1) }}
	genericOps["NeqB"] = &opSem{args: []want{wBool, wBool}, eval: func(c *ctx, n *node) val { return boolVal(n.args[0].i&1 != n.args[1].i&1) }}
	genericOps["CondSelect"] = &opSem{args: []want{wAny, wAny, wBool}, eval: func(c *ctx, n *node) val {
		if n.args[2].i&1 != 0 {
			return n.args[0]
		}
		return n.args[1]
	}}
	ptrCmp := func(name string, f func(c *ctx, x, y uint64) bool) {
		genericOps[name] = &opSem{args: wInts(2, 64), eval: func(c *ctx, n *node) val {
			w := c.a.ptrW
			return boolVal(f(c, trunc(n.args[0].i, w), trunc(n.args[1].i, w)))
		}}
	}
	ptrCmp("EqPtr", func(c *ctx, x, y uint64) bool { return x == y })
	ptrCmp("NeqPtr", func(c *ctx, x, y uint64) bool { return x != y })
	// 0 <= idx < len, where len >= 0 (genericOps.go).
	ptrCmp("IsInBounds", func(c *ctx, idx, n uint64) bool {
		if sext(n, c.a.ptrW) < 0 {
			impossible()
		}
		return sext(idx, c.a.ptrW) >= 0 && sext(idx, c.a.ptrW) < sext(n, c.a.ptrW)
	})
	ptrCmp("IsSliceInBounds", func(c *ctx, idx, n uint64) bool {
		if sext(n, c.a.ptrW) < 0 {
			impossible()
		}
		return sext(idx, c.a.ptrW) >= 0 && sext(idx, c.a.ptrW) <= sext(n, c.a.ptrW)
	})
	genericOps["IsNonNil"] = &opSem{args: wInts(1, 64), eval: func(c *ctx, n *node) val {
		return boolVal(trunc(n.args[0].i, c.a.ptrW) != 0)
	}}
}

func init() {
	sel := func(i int) *opSem {
		return &opSem{args: []want{wAny}, eval: func(c *ctx, n *node) val {
			if n.args[0].k != kTuple {
				unmodeled("Select%d of %v", i, n.args[0])
			}
			return n.args[0].xs[i]
		}}
	}
	genericOps["Select0"] = sel(0)
	genericOps["Select1"] = sel(1)
}

func init() {
	// Add64carry x y c is (x+y+c, carry out), with c 0 or 1; Sub64borrow
	// likewise (genericOps.go).
	for _, name := range []string{"Add64carry", "Sub64borrow"} {
		sub := name == "Sub64borrow"
		genericOps[name] = &opSem{args: wInts(3, 64), eval: func(c *ctx, n *node) val {
			x, y, cin := n.args[0].i, n.args[1].i, n.args[2].i
			if cin > 1 {
				impossible()
			}
			var r, cout uint64
			if sub {
				r, cout = bits.Sub64(x, y, cin)
			} else {
				r, cout = bits.Add64(x, y, cin)
			}
			return val{k: kTuple, xs: []val{intVal(r, 64), intVal(cout, 64)}}
		}}
	}
}

func init() {
	// Shifts (genericOps.go): Lsh64x32 x y is x << y, with y an unsigned
	// 32-bit count; counts of the width or more shift everything out
	// (or, for signed right shifts, fill with the sign).
	for _, w := range []uint8{8, 16, 32, 64} {
		for _, cw := range []uint8{8, 16, 32, 64} {
			w, cw := w, cw
			sfx := fmt.Sprintf("%dx%d", w, cw)
			sh := func(name, k string) {
				genericOps[name] = &opSem{args: []want{wInt(w), wInt(cw)}, eval: func(c *ctx, n *node) val {
					return intVal(armShift(k, n.args[0].i, trunc(n.args[1].i, cw), w), w)
				}}
			}
			sh(fmt.Sprintf("Lsh%d", w)+"x"+fmt.Sprint(cw), "LL")
			sh(fmt.Sprintf("Rsh%dUx%d", w, cw), "RL")
			sh("Rsh"+sfx, "RA")
		}
	}
}

// shiftBounds returns the operand and count widths of a generic shift op.
func shiftBounds(op string) (w, cw uint8, ok bool) {
	var a, b int
	for _, f := range []string{"Lsh%dx%d", "Rsh%dUx%d", "Rsh%dx%d"} {
		if n, _ := fmt.Sscanf(op, f, &a, &b); n == 2 && fmt.Sprintf(f, a, b) == op {
			return uint8(a), uint8(b), true
		}
	}
	return 0, 0, false
}
