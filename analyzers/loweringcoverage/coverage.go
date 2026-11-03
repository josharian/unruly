package loweringcoverage

import (
	"fmt"
	"go/ast"
	"go/token"
	"maps"
	"slices"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// A point is one concrete generic value that may reach the lower pass.
type point struct {
	desc string
	t    *term
}

// knobDomains are the buildcfg settings that lowering conditions consult,
// with their valid values (internal/buildcfg/cfg.go: goamd64, goppc64).
var knobDomains = map[string][]int64{
	"GOAMD64": {1, 2, 3, 4},
	"GOPPC64": {8, 9, 10},
}

// checkCoverage reports generic ops whose lowering rules in set leave some
// point of the op's domain unmatched, so that the op would survive the
// lower pass ("not lowered" fatal error).
func checkCoverage(pass *analysis.Pass, ai *archInfo, m *matcher) {
	g := pass.Ops.Generic
	simd := simdSizes(m.set, g)
	for _, name := range []string{"Load", "Store", "ZeroSIMD", "Zero", "Move", "OffPtr"} {
		op := g.Op(name)
		if op == nil {
			continue
		}
		rs := m.set.ByOp[op]
		if len(rs) == 0 {
			continue
		}
		var pts []point
		switch name {
		case "Load", "Store":
			pts = valuePoints(ai, op, name == "Store", simd)
		case "ZeroSIMD":
			for _, s := range simd {
				st := simdType(s)
				pts = append(pts, point{desc: st.name, t: &term{op: op, typ: st}})
			}
		case "Zero", "Move":
			pts = sizePoints(ai, g, op)
		case "OffPtr":
			pts = offPtrPoints(ai, g, op)
		}
		knobs := knobCombos(rs)
		var gaps []string
		for _, p := range pts {
			for _, k := range knobs {
				if covered(m, rs, p.t, k) {
					continue
				}
				d := p.desc
				for _, kn := range slices.Sorted(maps.Keys(k)) {
					d += fmt.Sprintf(" %s=%d", kn, k[kn])
				}
				gaps = append(gaps, d)
				break
			}
		}
		if len(gaps) == 0 {
			continue
		}
		const show = 4
		more := ""
		if len(gaps) > show {
			more = fmt.Sprintf(" and %d more", len(gaps)-show)
			gaps = gaps[:show]
		}
		pass.Reportf(rs[0].Pos, "no %s lowering rule matches %s: %s%s; the generic op would reach codegen unlowered (\"not lowered\" compiler crash)",
			m.set.Arch.Name, pattern(name), strings.Join(gaps, "; "), more)
	}
}

func pattern(name string) string {
	switch name {
	case "Load":
		return "(Load <t> ptr mem)"
	case "Store":
		return "(Store {t} ptr val mem)"
	case "ZeroSIMD":
		return "(ZeroSIMD <t>)"
	case "Zero":
		return "(Zero [s] {t} ptr mem)"
	case "Move":
		return "(Move [s] {t} dst src mem)"
	case "OffPtr":
		return "(OffPtr [off] ptr)"
	}
	return name
}

func covered(m *matcher, rs []*rules.Rule, t *term, knobs map[string]int64) bool {
	for _, r := range rs {
		if res, _ := m.apply(r, t, knobs); res != no {
			return true
		}
	}
	return false
}

// knobCombos returns the combinations of buildcfg settings that rs's
// conditions consult.
func knobCombos(rs []*rules.Rule) []map[string]int64 {
	combos := []map[string]int64{nil}
	for knob, dom := range knobDomains {
		used := false
		for _, r := range rs {
			if strings.Contains(r.Cond, "buildcfg."+knob) {
				used = true
				break
			}
		}
		if !used {
			continue
		}
		var next []map[string]int64
		for _, c := range combos {
			for _, v := range dom {
				nc := map[string]int64{knob: v}
				for k, x := range c {
					nc[k] = x
				}
				next = append(next, nc)
			}
		}
		combos = next
	}
	return combos
}

func phi(g *ops.Arch, t *typ) *term {
	return &term{op: g.Op("Phi"), typ: t}
}

func memTerm(g *ops.Arch) *term {
	return phi(g, &typ{name: "mem", kind: tMem, size: 0, align: 0, ptrs: no})
}

// valuePoints returns Load or Store values of each type that can reach
// lowering. Their pointer and value arguments are Phis, which no lowering
// rule looks into.
func valuePoints(ai *archInfo, op *ops.Op, store bool, simd []int64) []point {
	g := op.Arch
	ts := valueTypes(ai.ptrSize, store)
	for _, s := range simd {
		ts = append(ts, simdType(s))
	}
	var pts []point
	for _, t := range ts {
		pt := &term{op: op, auxint: intVal(0), aux: val{k: vNil}}
		if store {
			pt.typ = &typ{name: "mem", kind: tMem, size: 0, align: 0, ptrs: no}
			pt.aux = typVal(t)
			pt.args = []*term{phi(g, ptrTo(t, ai.ptrSize)), phi(g, t), memTerm(g)}
		} else {
			pt.typ = t
			pt.args = []*term{phi(g, ptrTo(t, ai.ptrSize)), memTerm(g)}
		}
		pts = append(pts, point{desc: "t=" + t.name, t: pt})
	}
	return pts
}

// sizePoints returns Zero or Move values of each size and alignment.
// Sizes are multiples of the alignment, as every Go type's size is, and
// Zero and Move created for runtime calls (memclr, memmove) use a byte
// type with alignment 1.
func sizePoints(ai *archInfo, g *ops.Arch, op *ops.Op) []point {
	var sizes []int64
	for s := int64(1); s <= 3000; s++ {
		sizes = append(sizes, s)
	}
	sizes = append(sizes, 1<<16, 1<<16+8, 1<<20+4, 1<<31, 1<<31+8)
	var pts []point
	for _, s := range sizes {
		for _, a := range []int64{1, 2, 4, 8} {
			if s%a != 0 {
				continue
			}
			// The size of the aux type need not be s (memclr uses a
			// byte type), so leave it unknown.
			t := &typ{name: fmt.Sprintf("align %d", a), kind: tUnknown, size: -1, align: a, ptrs: maybe}
			pt := &term{op: op, auxint: intVal(s), aux: typVal(t), typ: &typ{name: "mem", kind: tMem, ptrs: no}}
			bp := ptrTo(t, ai.ptrSize)
			if op.Name == "Zero" {
				pt.args = []*term{phi(g, bp), memTerm(g)}
			} else {
				pt.args = []*term{phi(g, bp), phi(g, bp), memTerm(g)}
			}
			pts = append(pts, point{desc: fmt.Sprintf("s=%d t.Alignment()=%d", s, a), t: pt})
		}
	}
	return pts
}

// offPtrPoints returns OffPtr values with a range of offsets, of SP and of
// other pointers.
func offPtrPoints(ai *archInfo, g *ops.Arch, op *ops.Op) []point {
	offs := []int64{0, 8, -8, 1<<15 - 8, 1 << 15, -(1 << 15) - 8, 1<<31 - 8, -(1 << 31)}
	if ai.ptrSize == 8 {
		offs = append(offs, 1<<31, 1<<40, -(1 << 40))
	}
	bp := typNames(ai.ptrSize)["BytePtr"]
	var pts []point
	for _, off := range offs {
		for _, sp := range []bool{false, true} {
			base := phi(g, bp)
			desc := fmt.Sprintf("off=%d", off)
			if sp {
				base = &term{op: g.Op("SP"), typ: typNames(ai.ptrSize)["Uintptr"]}
				desc += " ptr=SP"
			}
			pts = append(pts, point{desc: desc, t: &term{op: op, typ: bp, auxint: intVal(off), aux: val{k: vNil}, args: []*term{base}}})
		}
	}
	return pts
}

// simdSizes returns the sizes of the SIMD types that set's Load, Store,
// and ZeroSIMD lowerings handle: N in a "t.Size() == N" conjunct of a
// ZeroSIMD rule, or of a Load or Store rule where N > 8 (wider than any
// scalar) or the rule also requires t.IsSIMD().
func simdSizes(set *rules.RuleSet, g *ops.Arch) []int64 {
	seen := map[int64]bool{}
	var sizes []int64
	for _, name := range []string{"Load", "Store", "ZeroSIMD"} {
		for _, r := range set.ByOp[g.Op(name)] {
			var size int64
			isSIMD := name == "ZeroSIMD"
			for _, c := range conjuncts(r.CondExpr) {
				if n, ok := sizeEq(c); ok {
					size = n
				}
				if isMethodCall(c, "IsSIMD") {
					isSIMD = true
				}
			}
			if size > 8 || size > 0 && isSIMD {
				if !seen[size] {
					seen[size] = true
					sizes = append(sizes, size)
				}
			}
		}
	}
	return sizes
}

func conjuncts(x ast.Expr) []ast.Expr {
	switch y := x.(type) {
	case nil:
		return nil
	case *ast.ParenExpr:
		return conjuncts(y.X)
	case *ast.BinaryExpr:
		if y.Op == token.LAND {
			return append(conjuncts(y.X), conjuncts(y.Y)...)
		}
	}
	return []ast.Expr{x}
}

// sizeEq recognizes "t.Size() == N".
func sizeEq(x ast.Expr) (int64, bool) {
	b, ok := x.(*ast.BinaryExpr)
	if !ok || b.Op != token.EQL || !isMethodCall(b.X, "Size") {
		return 0, false
	}
	e := &env{arch: &archInfo{ptrSize: 8}, vars: map[string]val{}}
	if v := e.eval(b.Y); v.k == vInt {
		return v.i, true
	}
	return 0, false
}

func isMethodCall(x ast.Expr, name string) bool {
	c, ok := x.(*ast.CallExpr)
	if !ok || len(c.Args) != 0 {
		return false
	}
	sel, ok := c.Fun.(*ast.SelectorExpr)
	return ok && sel.Sel.Name == name
}
