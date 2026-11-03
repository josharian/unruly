// Package prior adds to a rule's facts what the earlier rules for its op
// imply: a rule fires only if every earlier rule that would match the same
// value did not fire, so their conditions were false.
//
// For example, generic.rules has
//
//	((Lsh64|Rsh64U)x64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])
//
// before
//
//	(Lsh64x64 (And64 (Rsh64x64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c >= e => ...
//
// so when the second fires, e is in [0, 63].
package prior

import (
	"go/ast"
	"go/types"
	"math/big"
	"strings"

	"github.com/josharian/unruly/analyzers/shadow/term"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// Facts returns f, the facts of rule r, extended with the negated
// condition of each rule that precedes r for the same op or block kind
// and certainly matches every value that r matches. An earlier rule's
// condition is used only if each of its variables is bound to one of r's
// match variables.
func Facts(res *typecheck.Result, r *rules.Rule, f *facts.Facts) *facts.Facts {
	tr := res.Rule(r)
	if tr == nil {
		return f
	}
	var group []*rules.Rule
	if r.IsBlock() {
		group = r.Set.ByBlock[r.MatchBlock.Info]
	} else if r.Match.Op != nil {
		group = r.Set.ByOp[r.Match.Op]
	}
	var t *target
	for _, p := range group {
		if p == r {
			break
		}
		ptr := res.Rule(p)
		if ptr == nil {
			continue
		}
		if ptr.Cond == nil {
			f = excludeLiterals(r, p, f)
			continue
		}
		if t == nil {
			t = newTarget(r, tr)
		}
		t.each(p, func(b term.Binding) {
			if bind, ok := t.bind(res.Info, ptr, b); ok {
				f = f.AssumeNot(ptr.Cond, bind)
			}
		})
	}
	return f
}

// A target is the rule whose facts are being extended, as terms.
type target struct {
	r      *rules.Rule
	ts     []*term.Term
	auxInt term.Field
	aux    term.Field
	idents map[string]ast.Expr // r's match variables' identifiers
}

func newTarget(r *rules.Rule, tr *typecheck.Rule) *target {
	vars := r.MatchVars()
	rename := func(name string) (string, bool) {
		_, ok := vars[name]
		return name, ok
	}
	b := &term.Builder{Syms: new(term.Symbols), Rename: rename}
	t := &target{r: r, idents: map[string]ast.Expr{}}
	if r.IsBlock() {
		t.ts = b.Match(r.MatchBlock.Controls...)
		t.auxInt = b.Field(r.MatchBlock.AuxInt)
		t.aux = b.Field(r.MatchBlock.Aux)
	} else {
		t.ts = b.Match(r.Match)
	}
	for name, occs := range vars {
		o := occs[0]
		var node any = o.Value
		if o.Value == nil {
			node = r.MatchBlock
		}
		var fld typecheck.Field
		switch o.Kind {
		case rules.OccValue:
			fld = typecheck.Name
		case rules.OccType:
			fld = typecheck.Type
		case rules.OccAuxInt:
			fld = typecheck.AuxInt
		case rules.OccAux:
			fld = typecheck.Aux
		}
		if e := tr.Expr(node, fld); e != nil {
			t.idents[name] = e
		}
	}
	return t
}

// each calls fn with each binding under which p certainly matches t.
func (t *target) each(p *rules.Rule, fn func(term.Binding)) {
	k := func(b term.Binding) bool {
		fn(b)
		return false
	}
	if !p.IsBlock() {
		term.MatchValue(p.Match, t.ts[0], term.Binding{}, k)
		return
	}
	pb := p.MatchBlock
	term.MatchField(pb.AuxInt, t.auxInt, term.Binding{}, func(b term.Binding) bool {
		return term.MatchField(pb.Aux, t.aux, b, func(b term.Binding) bool {
			return term.MatchValues(pb.Controls, t.ts, b, k)
		})
	})
}

// bind returns, for each variable of p's condition, the identifier of the
// variable of t.r it is bound to under b.
func (t *target) bind(info *types.Info, ptr *typecheck.Rule, b term.Binding) (map[types.Object]ast.Expr, bool) {
	vars := map[types.Object]string{}
	for name, v := range ptr.Vars {
		vars[v] = name
	}
	bind := map[types.Object]ast.Expr{}
	ok := true
	ast.Inspect(ptr.Cond, func(n ast.Node) bool {
		id, isID := n.(*ast.Ident)
		if !isID || !ok {
			return ok
		}
		obj := info.Uses[id]
		name, isVar := vars[obj]
		if !isVar {
			return true
		}
		sym, found := b.Lookup(name)
		e := t.idents[sym]
		if !found || e == nil {
			ok = false
			return false
		}
		bind[obj] = e
		return true
	})
	return bind, ok
}

// excludeLiterals returns f extended with what unconditional earlier rule
// p implies: if p matches r's values except that it requires a literal
// auxint where r binds a variable, as in
//
//	(Select0 (MULTU (MOVWconst [1]) _)) => (MOVWconst [0])
//	(Select0 (MULTU (MOVWconst [c]) x)) && ssa.IsPowerOfTwo(uint32(c)) => ...
//
// then that variable is not that literal (c != 1) when r fires.
func excludeLiterals(r, p *rules.Rule, f *facts.Facts) *facts.Facts {
	if r.IsBlock() || p.IsBlock() {
		return f
	}
	var lits []string
	p.Match.Walk(func(v *rules.Value) bool {
		if v.Op != nil && v.AuxInt != "" && v.AuxInt != "_" && !rules.IsVarText(v.AuxInt) {
			lits = append(lits, v.AuxInt)
		}
		return true
	})
	if len(lits) == 0 {
		return f
	}
	for name, occs := range r.MatchVars() {
		if len(occs) != 1 || occs[0].Kind != rules.OccAuxInt || occs[0].Value == nil {
			continue
		}
		for _, lit := range lits {
			x, ok := new(big.Int).SetString(strings.TrimSpace(lit), 0)
			if !ok {
				continue
			}
			m := withAuxInt(r.Match, occs[0].Value, lit)
			vars := map[string]bool{}
			for n := range r.MatchVars() {
				vars[n] = n != name
			}
			b := &term.Builder{Syms: new(term.Symbols), Rename: func(n string) (string, bool) { return n, vars[n] }}
			t := b.Match(m)[0]
			if term.MatchValue(p.Match, t, term.Binding{}, func(term.Binding) bool { return true }) {
				f = f.ExcludeVar(name, x)
			}
		}
	}
	return f
}

// withAuxInt returns a copy of v in which node n's auxint is text.
func withAuxInt(v, n *rules.Value, text string) *rules.Value {
	c := *v
	if v == n {
		c.AuxInt = text
	}
	c.Args = make([]*rules.Value, len(v.Args))
	for i, a := range v.Args {
		c.Args[i] = withAuxInt(a, n, text)
	}
	return &c
}
