package rewritecycle

import (
	"maps"
	"strings"

	"github.com/josharian/unruly/analyzers/shadow/term"
)

// subst is a substitution for the symbols of terms: value symbols map to
// terms, field symbols to fields. It is immutable.
type subst struct {
	vals   map[string]*term.Term
	fields map[string]term.Field
}

func (s subst) bindVal(sym string, t *term.Term) subst {
	vals := maps.Clone(s.vals)
	if vals == nil {
		vals = map[string]*term.Term{}
	}
	vals[sym] = t
	return subst{vals, s.fields}
}

func (s subst) bindField(sym string, f term.Field) subst {
	fields := maps.Clone(s.fields)
	if fields == nil {
		fields = map[string]term.Field{}
	}
	fields[sym] = f
	return subst{s.vals, fields}
}

// resolve follows the bindings of leaf t.
func (s subst) resolve(t *term.Term) *term.Term {
	for t.Op == nil && !t.Rigid {
		u, ok := s.vals[t.Sym]
		if !ok || u == t {
			break
		}
		t = u
	}
	return t
}

// sym returns the symbol that sym currently stands for.
func (s subst) sym(sym string) string {
	for range 100 {
		u, ok := s.vals[sym]
		if !ok || u.Sym == sym {
			return sym
		}
		sym = u.Sym
	}
	return sym
}

// field resolves f, substituting into expressions.
func (s subst) field(f term.Field) term.Field {
	for range 100 {
		if f.Sym == "" {
			break
		}
		g, ok := s.fields[f.Sym]
		if !ok {
			return f
		}
		f = g
	}
	if f.Expr != "" {
		f.Expr = term.Fold(s.text(f.Expr))
	}
	return f
}

// text substitutes s's bindings into Go expression e.
func (s subst) text(e string) string {
	for range 10 {
		changed := false
		e2 := term.Subst(e, func(name string) (string, bool) {
			if _, ok := s.vals[name]; ok {
				if r := s.sym(name); r != name {
					changed = true
					return r, true
				}
				return "", false
			}
			if f, ok := s.fields[name]; ok && f.String() != name {
				changed = true
				return f.String(), true
			}
			return "", false
		})
		if !changed {
			return e
		}
		e = e2
	}
	return e
}

// apply returns t with s's bindings applied throughout.
func (s subst) apply(t *term.Term) *term.Term {
	memo := map[*term.Term]*term.Term{}
	var ap func(t *term.Term) *term.Term
	ap = func(t *term.Term) *term.Term {
		t = s.resolve(t)
		if u, ok := memo[t]; ok {
			return u
		}
		if t.Op == nil {
			return t
		}
		u := &term.Term{
			Op:     t.Op,
			Sym:    t.Sym,
			Type:   s.field(t.Type),
			AuxInt: s.field(t.AuxInt),
			Aux:    s.field(t.Aux),
			Rest:   t.Rest,
		}
		memo[t] = u
		for _, a := range t.Args {
			u.Args = append(u.Args, ap(a))
		}
		return u
	}
	return ap(t)
}

func (s subst) occurs(sym string, t *term.Term) bool {
	t = s.resolve(t)
	if t.Op == nil {
		return t.Sym == sym
	}
	for _, a := range t.Args {
		if s.occurs(sym, a) {
			return true
		}
	}
	return false
}

// unify calls k with each most general substitution extending s under
// which pattern p and term t are the same value, until k returns true.
// Leaves of both sides that are not rigid may be refined. Commutative
// ops unify in either argument order. Field expressions unify only when
// they are certainly equal, so unify never claims a match that might
// not exist.
func unify(p, t *term.Term, s subst, k func(subst) bool) bool {
	return unifyTyped(p, t, s, true, k)
}

// unifyTyped is unify, ignoring types unless typed is set.
func unifyTyped(p, t *term.Term, s subst, typed bool, k func(subst) bool) bool {
	p, t = s.resolve(p), s.resolve(t)
	switch {
	case p == t:
		return k(s)
	case p.Op == nil && t.Op == nil && p.Sym == t.Sym:
		return k(s)
	case p.Op == nil && !p.Rigid:
		if s.occurs(p.Sym, t) {
			return false
		}
		return k(s.bindVal(p.Sym, t))
	case t.Op == nil && !t.Rigid:
		if s.occurs(t.Sym, p) {
			return false
		}
		return k(s.bindVal(t.Sym, p))
	case p.Op == nil || t.Op == nil || p.Op != t.Op:
		return false
	}
	n := len(t.Args)
	switch {
	case p.Rest && t.Rest:
		n = min(len(p.Args), len(t.Args))
	case p.Rest:
		if len(t.Args) < len(p.Args) {
			return false
		}
		n = len(p.Args)
	case t.Rest:
		if len(p.Args) < len(t.Args) {
			return false
		}
	default:
		if len(p.Args) != len(t.Args) {
			return false
		}
	}
	if p.Sym != t.Sym {
		if _, ok := s.vals[p.Sym]; !ok {
			s = s.bindVal(p.Sym, t)
		}
	}
	ok := true
	if typed {
		if s, ok = unifyField(p.Type, t.Type, s); !ok {
			return false
		}
	}
	if s, ok = unifyField(p.AuxInt, t.AuxInt, s); !ok {
		return false
	}
	if s, ok = unifyField(p.Aux, t.Aux, s); !ok {
		return false
	}
	pa, ta := p.Args[:n], t.Args[:n]
	if unifyArgs(pa, ta, s, typed, k) {
		return true
	}
	if p.Op.Commutative && n >= 2 {
		swapped := append([]*term.Term{ta[1], ta[0]}, ta[2:]...)
		return unifyArgs(pa, swapped, s, typed, k)
	}
	return false
}

func unifyArgs(ps, ts []*term.Term, s subst, typed bool, k func(subst) bool) bool {
	if len(ps) == 0 {
		return k(s)
	}
	return unifyTyped(ps[0], ts[0], s, typed, func(s subst) bool {
		return unifyArgs(ps[1:], ts[1:], s, typed, k)
	})
}

func unifyField(f, g term.Field, s subst) (subst, bool) {
	f, g = s.field(f), s.field(g)
	switch {
	case f == g:
		return s, true
	case f.Sym != "":
		return s.bindField(f.Sym, g), !mentions(g, f.Sym)
	case g.Sym != "":
		return s.bindField(g.Sym, f), !mentions(f, g.Sym)
	case f.Expr == "" || g.Expr == "":
		return s, false
	case term.SameExpr(f.Expr, g.Expr):
		return s, true
	}
	if s, ok := solve(f.Expr, g.Expr, s); ok {
		return s, true
	}
	return solve(g.Expr, f.Expr, s)
}

// solve tries to make expression e equal to constant k by binding the
// one field symbol in e to k, as when [int32(c)] must equal [-1].
func solve(e, k string, s subst) (subst, bool) {
	if term.Eval(k) == nil {
		return s, false
	}
	var sym string
	for _, id := range term.Idents(e) {
		if _, ok := s.fields[id]; ok || !isSym(id) {
			continue
		}
		if sym != "" && sym != id {
			return s, false
		}
		sym = id
	}
	if sym == "" {
		return s, false
	}
	got := term.Subst(e, func(name string) (string, bool) {
		if name == sym {
			return k, true
		}
		return "", false
	})
	if !term.SameExpr(got, k) {
		return s, false
	}
	return s.bindField(sym, term.Field{Expr: term.Fold(k)}), true
}

// isSym reports whether id is a renamed rule variable.
func isSym(id string) bool {
	return strings.Contains(id, "ǀ")
}

// equal reports whether a and b are certainly the same value, up to
// commutativity, ignoring types.
func equal(a, b *term.Term, s subst) bool {
	a, b = s.resolve(a), s.resolve(b)
	if a == b || a.Op == nil && b.Op == nil && a.Sym == b.Sym {
		return true
	}
	if a.Op == nil || b.Op == nil || a.Op != b.Op || len(a.Args) != len(b.Args) || a.Rest || b.Rest {
		return false
	}
	if !sameField(a.AuxInt, b.AuxInt, s) || !sameField(a.Aux, b.Aux, s) {
		return false
	}
	eq := func(bs []*term.Term) bool {
		for i := range a.Args {
			if !equal(a.Args[i], bs[i], s) {
				return false
			}
		}
		return true
	}
	if eq(b.Args) {
		return true
	}
	if a.Op.Commutative && len(b.Args) >= 2 {
		return eq(append([]*term.Term{b.Args[1], b.Args[0]}, b.Args[2:]...))
	}
	return false
}

func sameField(f, g term.Field, s subst) bool {
	f, g = s.field(f), s.field(g)
	if f == g {
		return true
	}
	if f.Sym != "" || g.Sym != "" || f.Expr == "" || g.Expr == "" {
		return false
	}
	return term.SameExpr(f.Expr, g.Expr)
}

// mentions reports whether field f's expression refers to sym.
func mentions(f term.Field, sym string) bool {
	if f.Expr == "" {
		return false
	}
	for _, id := range term.Idents(f.Expr) {
		if id == sym {
			return true
		}
	}
	return false
}
