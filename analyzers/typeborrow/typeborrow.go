// Package typeborrow reports result values whose type is borrowed from a
// matched value but does not fit the bits the new value holds.
package typeborrow

import (
	"fmt"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "typeborrow",
	Doc: `report result values typed with a borrowed type that cannot hold them

A value's type decides how it is spilled and reloaded (by size and
signedness), how CSE and later rules treat it (t.Size()-driven folds),
and whether the GC sees it as a pointer. Rules often give a new value
the type of a matched value, as <t>, <x.Type>, or <v.Type>. When the new
value's meaningful bits don't fit that type, the value is silently
corrupted once something consults the type. typeborrow reports:

  - A constant left shift typed with a type that may be narrower than
    the shift amount, so the type's bits are all zero and the value
    lives entirely above them. RISCV64latelower once had
    (SRAI [c] (MOVBreg x)) && c < 8 => (SRAI [56+c] (SLLI <t> [56] x)),
    where t is the int8 type of a lowered Rsh8x64; fixed by 2952fe4f16.

  - A value stored by an n-byte store, typed with a type that may be
    narrower than n bytes. AMD64 had
    (MOVBstore [i] {s} p w x0:(MOVBstore [i-1] {s} p (SHRWconst [8] w) mem))
      => (MOVWstore [i-1] {s} p (ROLWconst <w.Type> [8] w) mem),
    where w may be a uint8; a spill of the ROLWconst kept one byte.
    Fixed by b3bc8620f8.

  - A new pointer-width load left at its op's integer default type while
    it is compared against a matched value x, which may be a pointer: the
    loaded value should be <x.Type>. Fixed in AMD64splitload by 80123ef4bf.

  - A projection (StructSelect, Select0, ...) rewritten to its own matched
    argument, as in (StructSelect [0] x:(IData _)) => x, which replaces a
    field with the whole struct value. Fixed by 70331a31ed.

The width of a borrowed type is bounded below by what the match and
condition establish: a generic op's width, a t.Size() == n or
ssa.Is64BitInt(t) condition. Values of arch ops carry the types of the
generic values they lower, so they may be as narrow as 8 bits.
Arch facts (constant-shift ops, store widths, pointer size) are derived
from the arch's own lowering rules.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	facts := deriveFacts(pass.Corpus)
	for r := range pass.Rules() {
		f := facts[r.Set.Arch]
		for _, res := range r.ResultValues() {
			walk(nil, -1, res, func(parent *rules.Value, idx int, v *rules.Value) {
				if parent != nil {
					narrowShift(pass, r, f, v)
					loadCompare(pass, r, f, parent, idx, v)
				}
				storeWidth(pass, r, f, v)
			})
		}
		projection(pass, r)
	}
	return nil
}

func walk(parent *rules.Value, idx int, v *rules.Value, f func(parent *rules.Value, idx int, v *rules.Value)) {
	if v.IsLeaf() {
		return
	}
	f(parent, idx, v)
	for i, a := range v.Args {
		walk(v, i, a, f)
	}
}

// narrowShift reports (SHLconst <t> [k] x) where t may be narrower than k bits.
func narrowShift(pass *analysis.Pass, r *rules.Rule, f *archFacts, v *rules.Value) {
	if f == nil || !f.lshConst[v.Op] || v.Type == "" {
		return
	}
	k, err := strconv.ParseInt(v.AuxInt, 0, 64)
	if err != nil {
		return
	}
	s, ok := resolve(r, v.Type)
	if !ok {
		return
	}
	if w := minBits(r, s, f); k >= int64(w) {
		lost := "a spill (sized by the type) or a rule that tests t.Size()"
		if sr := sizeRule(r.Set, v.Op); sr != nil {
			lost = fmt.Sprintf("a spill (sized by the type) or %s:%d, which tests the %s's t.Size()", filepath.Base(sr.Pos.File), sr.Pos.Line, v.Op.Name)
		}
		pass.Reportf(r.Pos, "(%s <%s> [%d] ...) has only zeros in its type's bits: %s, which may be %d bits wide, so the value lives entirely above its type and is lost by %s; use a full-width type such as typ.UInt64",
			v.Op.Name, v.Type, k, s.describe(r), w, lost)
	}
}

// sizeRule returns a rule of set for op whose condition tests the size of
// the matched value's type, such as
// (SLLI <t> [c] (ADD x x)) && c >= t.Size() * 8 - 1 => (MOVDconst [0]), or nil.
func sizeRule(set *rules.RuleSet, op *ops.Op) *rules.Rule {
	for _, r := range set.ByOp[op] {
		if rules.IsVarText(r.Match.Type) && strings.Contains(r.Cond, r.Match.Type+".Size()") {
			return r
		}
	}
	return nil
}

// storeWidth reports an n-byte store of a new value typed with a type that
// may be narrower than n bytes.
func storeWidth(pass *analysis.Pass, r *rules.Rule, f *archFacts, v *rules.Value) {
	if f == nil {
		return
	}
	st, ok := f.stores[v.Op]
	if !ok || st.val >= len(v.Args) {
		return
	}
	val := v.Args[st.val]
	if val.IsLeaf() || val.Type == "" {
		return
	}
	s, ok := resolve(r, val.Type)
	if !ok {
		return
	}
	if w := minBits(r, s, f); w < 8*st.bytes {
		pass.Reportf(r.Pos, "%s stores %d bytes of (%s <%s> ...), but %s, which may be %d bits wide; a spill of the %s keeps only its type's bytes; use a %d-byte type",
			v.Op.Name, st.bytes, val.Op.Name, val.Type, s.describe(r), w, val.Op.Name, st.bytes)
	}
}

// loadCompare reports (CMP (MOVload ...) x) where the new load has an
// integer default type although it may load a pointer like x.
func loadCompare(pass *analysis.Pass, r *rules.Rule, f *archFacts, parent *rules.Value, idx int, v *rules.Value) {
	if f == nil || f.ptrBytes == 0 || !isCompare(parent.Op) || len(parent.Args) != 2 {
		return
	}
	if _, src := r.ResultType(v); src != rules.TypeOpDefault {
		return
	}
	if !strings.Contains(v.Op.SymEffect, "Read") || typeBytes(v.Op.Typ) != f.ptrBytes || isFloat(v.Op.Typ) {
		return
	}
	other := parent.Args[1-idx]
	if !other.IsVar() || !isMatchValue(r, other.Name) {
		return
	}
	pass.Reportf(r.Pos, "(%s ...) compared with %s gets %s's default type %s, but it loads a value of %s's type, which may be a pointer; give it <%s.Type>",
		v.Op.Name, other.Name, v.Op.Name, v.Op.Typ, other.Name, other.Name)
}

// isMatchValue reports whether name is a value variable bound by r's match
// (not the name of a result sub-expression).
func isMatchValue(r *rules.Rule, name string) bool {
	for _, o := range r.MatchVars()[name] {
		if o.Kind == rules.OccValue {
			return true
		}
	}
	return false
}

// isCompare reports whether op compares two general-purpose registers,
// producing flags.
func isCompare(op *ops.Op) bool {
	if op.IsGeneric() || op.Typ != "Flags" || op.ArgLength != 2 || len(op.Reg.Inputs) != 2 {
		return false
	}
	for _, in := range op.Reg.Inputs {
		// The allowed registers may include SP, as in AMD64's gpsp.
		if c := op.Arch.Classify(in); c&ops.RegGP == 0 || c&(ops.RegFP|ops.RegSIMD|ops.RegSIMDMask) != 0 {
			return false
		}
	}
	return true
}

func isFloat(typ string) bool { return strings.HasPrefix(typ, "Float") }

// projection reports (Proj x:(Op ...)) => x for a projection Proj, which
// replaces the projected part with the whole aggregate.
func projection(pass *analysis.Pass, r *rules.Rule) {
	if r.IsBlock() || r.Result == nil || !r.Result.IsVar() || len(r.Match.Args) == 0 || !isProjection(r.Match.Op) {
		return
	}
	x := r.Match.Args[0]
	if x.IsLeaf() || x.Name != r.Result.Name {
		return
	}
	pass.Reportf(r.Pos, "result %s is the %s that %s projects from, so the %s (type of a part) is replaced by a value of the aggregate's type; rebuild the projection around %s's arguments instead",
		x.Name, x.Op.Name, r.Match.Op.Name, r.Match.Op.Name, x.Name)
}

// isProjection reports whether op extracts a part of its first argument.
func isProjection(op *ops.Op) bool {
	switch op.Name {
	case "StructSelect", "ArraySelect":
		return op.IsGeneric()
	}
	sig, ok := opsig.Lookup(op)
	if !ok || len(sig.Args) == 0 {
		return false
	}
	switch sig.Args[0].Kind {
	case opsig.Tuple, opsig.Results, opsig.String, opsig.Slice, opsig.Interface, opsig.Complex, opsig.Struct, opsig.Array:
		return sig.Result.Kind != sig.Args[0].Kind
	}
	return false
}
