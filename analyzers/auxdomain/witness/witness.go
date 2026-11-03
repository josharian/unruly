// Package witness searches for values of a rule's variables that show a
// suspected defect: values that satisfy the rule's condition (and
// whatever else its facts assume) and make some expression go wrong.
package witness

import (
	"cmp"
	"fmt"
	"go/ast"
	"go/types"
	"math/big"
	"slices"
	"strings"

	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// A Witness is an assignment of values to a rule's integer and boolean
// variables.
type Witness struct {
	Vals  map[types.Object]any
	names []string
	objs  map[string]types.Object
}

// String formats w as "c=63 d=0", in the order of the variables' names.
func (w *Witness) String() string {
	var parts []string
	for _, n := range w.names {
		v := w.Vals[w.objs[n]]
		if x, ok := v.(*big.Int); ok && x.CmpAbs(big.NewInt(1<<16)) > 0 {
			// Large values are clearer in hex: 0x300000000.
			v = fmt.Sprintf("%#x", x)
			if x.Sign() < 0 {
				v = fmt.Sprintf("-%#x", new(big.Int).Neg(x))
			}
		}
		parts = append(parts, n+"="+fmt.Sprint(v))
	}
	return strings.Join(parts, " ")
}

// Search returns values of r's integer and boolean match variables for
// which f.Holds and bad reports true, or nil if it finds none. It tries
// the edges of each variable's range (from f) first, then other edge
// cases, then random combinations of them.
func Search(f *facts.Facts, res *typecheck.Result, r *rules.Rule, bad func(vals map[types.Object]any) bool) *Witness {
	tr := res.Rule(r)
	if tr == nil {
		return nil
	}
	w := &Witness{objs: map[string]types.Object{}}
	var cands [][]any
	for name, occs := range r.MatchVars() {
		obj := tr.Vars[name]
		if obj == nil {
			continue
		}
		var cs []any
		switch {
		case isBool(obj.Type()):
			cs = []any{false, true}
		case isInt(obj.Type()):
			cs = intCandidates(f, ident(tr, r, occs[0]), obj.Type())
		default:
			continue
		}
		w.names = append(w.names, name)
		w.objs[name] = obj
		cands = append(cands, cs)
	}
	// Sort for determinism; keep cands aligned.
	idx := make([]int, len(w.names))
	for i := range idx {
		idx[i] = i
	}
	slices.SortFunc(idx, func(a, b int) int { return cmp.Compare(w.names[a], w.names[b]) })
	names := make([]string, len(idx))
	sorted := make([][]any, len(idx))
	for i, j := range idx {
		names[i], sorted[i] = w.names[j], cands[j]
	}
	w.names, cands = names, sorted

	try := func(choice []int) bool {
		vals := map[types.Object]any{}
		for i, n := range w.names {
			vals[w.objs[n]] = cands[i][choice[i]]
		}
		if !f.Holds(vals) || !bad(vals) {
			return false
		}
		w.Vals = vals
		return true
	}

	// Try combinations in order of their largest candidate index, so
	// that simple values are tried together first.
	maxLen := 0
	for _, cs := range cands {
		maxLen = max(maxLen, len(cs))
	}
	budget := 1 << 17
	choice := make([]int, len(cands))
	var level func(i, lim int, hit bool) bool
	level = func(i, lim int, hit bool) bool {
		if budget <= 0 {
			return false
		}
		if i == len(cands) {
			if !hit {
				return false
			}
			budget--
			return try(choice)
		}
		for j := 0; j <= lim && j < len(cands[i]); j++ {
			choice[i] = j
			if level(i+1, lim, hit || j == lim) {
				return true
			}
		}
		return false
	}
	for lim := range maxLen {
		if level(0, lim, false) {
			return w
		}
		if budget <= 0 {
			break
		}
	}
	if len(cands) == 0 && try(choice) {
		return w
	}
	return nil
}

// ident returns the identifier that binds variable o.
func ident(tr *typecheck.Rule, r *rules.Rule, o rules.Occurrence) ast.Expr {
	var node any = o.Value
	if o.Value == nil {
		node = r.MatchBlock
	}
	switch o.Kind {
	case rules.OccAuxInt:
		return tr.Expr(node, typecheck.AuxInt)
	case rules.OccAux:
		return tr.Expr(node, typecheck.Aux)
	}
	return nil
}

// intCandidates returns values of integer type t to try for the variable
// id, within its known range: small values, values near powers of two,
// and the edges of the range.
func intCandidates(f *facts.Facts, id ast.Expr, t types.Type) []any {
	tr, _ := facts.TypeRange(t)
	known := tr
	if id != nil {
		if iv, ok := f.Range(id); ok {
			known = iv
		}
	}
	var out []any
	seen := map[string]bool{}
	add := func(x *big.Int) {
		if x == nil || !within(x, known) || seen[x.String()] {
			return
		}
		seen[x.String()] = true
		out = append(out, x)
	}
	for x := int64(0); x <= 16; x++ {
		add(big.NewInt(x))
	}
	for k := uint(4); k <= 64; k++ {
		p := new(big.Int).Lsh(big.NewInt(1), k)
		for _, d := range []int64{-1, 0, 1} {
			add(new(big.Int).Add(p, big.NewInt(d)))
		}
	}
	add(big.NewInt(-1))
	add(big.NewInt(-2))
	for k := uint(4); k <= 64; k++ {
		p := new(big.Int).Lsh(big.NewInt(-1), k)
		for _, d := range []int64{-1, 0, 1} {
			add(new(big.Int).Add(p, big.NewInt(d)))
		}
	}
	// Multiples used by strength reduction: 3, 5, 9 times a power of two.
	for k := uint(4); k <= 64; k++ {
		p := new(big.Int).Lsh(big.NewInt(1), k)
		for _, m := range []int64{3, 5, 7, 9} {
			add(new(big.Int).Mul(p, big.NewInt(m)))
		}
	}
	for d := range int64(3) {
		if known.Lo != nil {
			add(new(big.Int).Add(known.Lo, big.NewInt(d)))
		}
		if known.Hi != nil {
			add(new(big.Int).Sub(known.Hi, big.NewInt(d)))
		}
	}
	return out
}

func isInt(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	return ok && b.Info()&types.IsInteger != 0
}

func isBool(t types.Type) bool {
	b, ok := t.Underlying().(*types.Basic)
	return ok && b.Info()&types.IsBoolean != 0
}

func within(x *big.Int, iv facts.Interval) bool {
	return (iv.Lo == nil || iv.Lo.Cmp(x) <= 0) && (iv.Hi == nil || x.Cmp(iv.Hi) <= 0)
}
