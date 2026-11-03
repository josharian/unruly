package loweringcoverage

import (
	"fmt"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// memWidths gives the number of bytes that an arch's load and store ops
// access, derived from the arch's own rules rather than from a table:
// the op that (Store {t} ...) lowers to writes t.Size() bytes, the load op
// in the lowering of (Load <t> ...) reads t.Size() bytes, and a store
// that a rule folds a constant into, such as
//
//	(MOVQstore [off] {sym} ptr (MOVQconst [c]) mem) => (MOVQstoreconst [...] {sym} ptr mem)
//
// writes as many bytes as the store it replaces.
type memWidths map[*ops.Op]int64

func deriveWidths(ai *archInfo, m *matcher, g *ops.Arch, simd []int64) memWidths {
	w := memWidths{}
	set := func(op *ops.Op, n int64) {
		if op == nil || op.IsGeneric() {
			return
		}
		if old, ok := w[op]; ok && old != n {
			w[op] = -1 // inconsistent; don't use
			return
		}
		w[op] = n
	}
	for _, store := range []bool{false, true} {
		op := g.Op("Load")
		if store {
			op = g.Op("Store")
		}
		for _, p := range valuePoints(ai, op, store, simd) {
			size := p.t.typ.size
			if store {
				size = p.t.aux.t.size
			}
			for _, r := range m.set.ByOp[op] {
				res, e := m.apply(r, p.t, nil)
				if res == no {
					continue
				}
				if res == yes {
					if out := m.build(r, p.t, e); out != nil {
						if mo := memOp(out); mo != nil {
							set(mo.op, size)
						}
					}
				}
				break
			}
		}
	}
	// Constant folds into stores. Only rules whose memory argument is a
	// plain variable qualify, which excludes store-combining rules.
	for changed := true; changed; {
		changed = false
		for _, r := range m.set.Rules {
			if r.IsBlock() || r.Result == nil || r.Result.Op == nil || r.Match.Op == nil {
				continue
			}
			from, to := r.Match.Op, r.Result.Op
			n, ok := w[from]
			if !ok || n < 0 || from == to || !isStore(from) || !isStore(to) {
				continue
			}
			if _, ok := w[to]; ok {
				continue
			}
			args := r.Match.Args
			if len(args) != 3 || !args[2].IsVar() || !isConst(args[1]) {
				continue
			}
			w[to] = n
			changed = true
		}
	}
	return w
}

// isStore and isLoad recognize an arch's plain memory ops: ops that
// write memory (symEffect Write, or result type Mem) or read it, whose
// first argument is the address (symEffect, faultOnNilArg0, or
// addrSinkArg0 says it is) and whose last is memory.
func isStore(op *ops.Op) bool {
	if op.Call || op.ArgLength < 2 || op.ArgLength > 3 {
		return false
	}
	return strings.Contains(op.SymEffect, "Write") || op.Typ == "Mem" && (op.FaultOnNilArg0 || op.AddrSinkArg0)
}

func isLoad(op *ops.Op) bool {
	if op.Call || op.ArgLength != 2 || op.Typ == "Mem" || strings.HasPrefix(op.Typ, "(") {
		return false
	}
	return op.SymEffect == "Read" || op.SymEffect == "" && (op.FaultOnNilArg0 || op.AddrSinkArg0)
}

// isConst reports whether match value v is a constant op with no args.
func isConst(v *rules.Value) bool {
	return v.Op != nil && len(v.Args) == 0 && strings.Contains(strings.ToLower(v.Op.Name), "const")
}

// memOp returns the first load or store in t, outermost first.
func memOp(t *term) *term {
	if t.op != nil && (isStore(t.op) || isLoad(t.op)) {
		return t
	}
	for _, a := range t.args {
		if m := memOp(a); m != nil {
			return m
		}
	}
	return nil
}

// An access is a load or store of width bytes at off from a base pointer.
type access struct {
	base  *term
	off   int64
	width int64
}

// address returns the base and offset that store or load t accesses.
func (w memWidths) address(t *term) (access, bool) {
	n, ok := w[t.op]
	if !ok || n <= 0 || len(t.args) == 0 {
		return access{}, false
	}
	var off int64
	switch t.op.AuxIntType {
	case "ValAndOff":
		if t.auxint.k != vInt {
			return access{}, false
		}
		off = int64(int32(t.auxint.i))
	case "int32", "int64":
		if t.auxint.k != vInt {
			return access{}, false
		}
		off = t.auxint.i
	case "invalid":
	default:
		return access{}, false
	}
	a, ok := offPtr(t.args[0])
	a.off += off
	a.width = n
	return a, ok
}

// offPtr returns the base and offset of pointer t, looking through
// generic OffPtrs.
func offPtr(t *term) (access, bool) {
	var off int64
	for t.op != nil && t.op.Name == "OffPtr" && t.op.IsGeneric() {
		if t.auxint.k != vInt {
			return access{}, false
		}
		off += t.auxint.i
		t = t.args[0]
	}
	return access{base: t, off: off}, true
}

// storedConst returns the constant that store t writes, if known: the
// value of a store-constant op's ValAndOff, or the auxint of a constant
// op stored by an ordinary store.
func storedConst(t *term) (int64, bool) {
	if t.op.AuxIntType == "ValAndOff" && len(t.args) == 2 {
		if t.auxint.k != vInt {
			return 0, false
		}
		return t.auxint.i >> 32, true
	}
	if len(t.args) != 3 {
		return 0, false
	}
	c := t.args[1]
	if c.op == nil || len(c.args) != 0 || !strings.Contains(strings.ToLower(c.op.Name), "const") || c.auxint.k != vInt {
		return 0, false
	}
	return c.auxint.i, true
}

// checkBytes reports Zero and Move lowerings of constant small sizes that
// don't write exactly the bytes [0, s): a gap leaves bytes unset, and a
// write past s clobbers a neighboring object. For Move, each store must
// write a load of the same bytes of the source, and for sizes at which
// isInlinableMemmove lets the source and destination overlap, every load
// must read the Move's incoming memory.
//
// It checks sizes up to 64 bytes at each alignment, and skips rule
// results whose ops' widths it cannot derive (see memWidths), such as
// loops and the Duff's devices.
func checkBytes(pass *analysis.Pass, ai *archInfo, m *matcher, w memWidths) {
	g := pass.Ops.Generic
	overlap := int64(-1) // largest Move size whose operands may overlap
	if src := loadSource(pass.Ops.Dir); src != nil {
		if n, ok := src.overlap[m.set.Arch.Name]; ok {
			overlap = n
		}
	}
	reported := map[*rules.Rule]bool{}
	for _, name := range []string{"Zero", "Move"} {
		op := g.Op(name)
		rs := m.set.ByOp[op]
		for _, p := range sizePoints(ai, g, op) {
			s := p.t.auxint.i
			if s > 64 {
				break
			}
			for _, k := range knobCombos(rs) {
				for _, r := range rs {
					res, e := m.apply(r, p.t, k)
					if res == no {
						continue
					}
					if res == yes && !reported[r] {
						if msg := w.checkLowering(name == "Move", s <= overlap, p.t, m.build(r, p.t, e)); msg != "" {
							reported[r] = true
							pass.Reportf(r.Pos, "%s lowering of %s: %s", m.set.Arch.Name, p.desc, msg)
						}
					}
					break
				}
			}
		}
	}
}

// checkLowering checks out, the lowering of Zero or Move t, and returns
// what is wrong with it, or "" if nothing is or it cannot tell.
func (w memWidths) checkLowering(move, overlap bool, t, out *term) string {
	if out == nil {
		return ""
	}
	s := t.auxint.i
	dst, mem := t.args[0], t.args[len(t.args)-1]
	var src *term
	if move {
		src = t.args[1]
	}
	written := make([]bool, s)
	var writes []string
	for cur := out; cur != mem; {
		if cur.op == nil {
			return ""
		}
		if cur.op.IsGeneric() && (cur.op.Name == "Zero" || cur.op.Name == "Move") {
			// A smaller Zero or Move, lowered by another rule.
			if (cur.op.Name == "Move") != move || cur.auxint.k != vInt {
				return ""
			}
			a, ok := offPtr(cur.args[0])
			if !ok || a.base != dst {
				return ""
			}
			a.width = cur.auxint.i
			if move {
				sa, ok := offPtr(cur.args[1])
				if !ok || sa.base != src || sa.off != a.off {
					return ""
				}
			}
			writes = append(writes, fmt.Sprintf("%s [%d,%d)", cur.op.Name, a.off, a.off+a.width))
			if a.off < 0 || a.off+a.width > s {
				return fmt.Sprintf("%s writes bytes [%d,%d), outside [0,%d)", cur.op.Name, a.off, a.off+a.width, s)
			}
			for i := a.off; i < a.off+a.width; i++ {
				written[i] = true
			}
			cur = cur.args[len(cur.args)-1]
			continue
		}
		if !isStore(cur.op) {
			return "" // something other than a chain of stores
		}
		a, ok := w.address(cur)
		if !ok || a.base != dst {
			return ""
		}
		if !move {
			if v, ok := storedConst(cur); ok && v != 0 {
				return fmt.Sprintf("%s stores %d, not 0", cur.op.Name, v)
			}
		}
		if move {
			if len(cur.args) != 3 {
				return ""
			}
			ld := cur.args[1]
			if ld.op == nil || !isLoad(ld.op) {
				return ""
			}
			la, ok := w.address(ld)
			if !ok || la.base != src {
				return ""
			}
			if la.off != a.off || la.width != a.width {
				return fmt.Sprintf("%s copies source bytes [%d,%d) to destination bytes [%d,%d)", cur.op.Name, la.off, la.off+la.width, a.off, a.off+a.width)
			}
			if overlap && ld.args[1] != mem {
				return fmt.Sprintf("%s reads memory after an earlier store of the copy, so an overlapping copy (allowed for small sizes by isInlinableMemmove) reads bytes it already overwrote", ld.op.Name)
			}
		}
		writes = append(writes, fmt.Sprintf("%s [%d,%d)", cur.op.Name, a.off, a.off+a.width))
		if a.off < 0 || a.off+a.width > s {
			return fmt.Sprintf("%s writes bytes [%d,%d), outside [0,%d)", cur.op.Name, a.off, a.off+a.width, s)
		}
		for i := a.off; i < a.off+a.width; i++ {
			written[i] = true
		}
		cur = cur.args[len(cur.args)-1]
	}
	for i, ok := range written {
		if !ok {
			return fmt.Sprintf("byte %d is not written (writes: %s)", i, strings.Join(writes, ", "))
		}
	}
	return ""
}

// checkable reports whether checkLowering can judge out (for tests).
func (w memWidths) checkable(move bool, t, out *term) bool {
	if out == nil {
		return false
	}
	mem := t.args[len(t.args)-1]
	for cur := out; cur != mem; cur = cur.args[len(cur.args)-1] {
		if cur.op == nil || !isStore(cur.op) {
			return false
		}
		if _, ok := w.address(cur); !ok {
			return false
		}
		if move {
			if len(cur.args) != 3 || cur.args[1].op == nil {
				return false
			}
			if _, ok := w.address(cur.args[1]); !ok {
				return false
			}
		}
	}
	return true
}
