// Package term represents rule patterns and the values that rules build as
// terms over symbols, and decides whether a rule certainly fires on a term.
//
// It is shared by the shadow and rewritecycle analyzers.
package term

import (
	"fmt"
	"maps"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// A Term is a value: a compound (Op != nil) with fields and args, or a
// leaf, an otherwise unknown value. Every term has a symbol, Sym, that
// names it in conditions; terms with the same symbol are the same value.
type Term struct {
	Op     *ops.Op
	Sym    string
	Type   Field
	AuxInt Field
	Aux    Field
	Args   []*Term
	Rest   bool // the value has at least len(Args) args, as in (Op x ___)
	// Rigid reports a leaf that unification may not refine: a value
	// computed by a Go expression in a result, such as x.Args[0].
	Rigid bool
}

// A Field is the type, auxint, or aux of a term: a symbol (Sym) or a Go
// expression (Expr) over symbols, in canonical form.
type Field struct {
	Sym  string
	Expr string
}

func (f Field) String() string {
	if f.Sym != "" {
		return f.Sym
	}
	return f.Expr
}

func (t *Term) String() string {
	var b strings.Builder
	t.write(&b)
	return b.String()
}

func (t *Term) write(b *strings.Builder) {
	if t.Op == nil {
		b.WriteString(t.Sym)
		return
	}
	b.WriteString("(" + t.Op.Name)
	if t.AuxInt.Expr != "" {
		b.WriteString(" [" + t.AuxInt.Expr + "]")
	}
	if t.Aux.Expr != "" {
		b.WriteString(" {" + t.Aux.Expr + "}")
	}
	for _, a := range t.Args {
		b.WriteByte(' ')
		a.write(b)
	}
	if t.Rest {
		b.WriteString(" ___")
	}
	b.WriteByte(')')
}

// Symbols makes fresh symbols. Fresh symbols contain a character that
// can't appear in a rule's variable names, so they never collide.
type Symbols struct{ n int }

// Fresh returns a new symbol.
func (s *Symbols) Fresh() string {
	s.n++
	return fmt.Sprintf("τ%d", s.n)
}

// Builder converts match patterns to terms.
type Builder struct {
	Syms *Symbols
	// Rename maps a rule's match variable to its symbol.
	// It reports false for names that are not match variables.
	Rename func(name string) (string, bool)

	named map[string]*Term
}

// Match returns the terms of the match values vals of one rule (a value
// rule's match or a block rule's controls). Each occurrence of a name
// bound to a compound value is that compound term, so the terms are DAGs.
// Unconstrained fields get fresh symbols.
func (b *Builder) Match(vals ...*rules.Value) []*Term {
	b.named = map[string]*Term{}
	for _, v := range vals {
		v.Walk(func(v *rules.Value) bool {
			if !v.IsLeaf() && v.Name != "" {
				if s, ok := b.Rename(v.Name); ok {
					b.named[s] = nil
				}
			}
			return true
		})
	}
	var ts []*Term
	for _, v := range vals {
		ts = append(ts, b.match(v))
	}
	// Replace leaves that name compounds built after them.
	seen := map[*Term]bool{}
	var fix func(t *Term) *Term
	fix = func(t *Term) *Term {
		if t.Op == nil {
			if c := b.named[t.Sym]; c != nil {
				return c
			}
			return t
		}
		if !seen[t] {
			seen[t] = true
			for i, a := range t.Args {
				t.Args[i] = fix(a)
			}
		}
		return t
	}
	for i, t := range ts {
		ts[i] = fix(t)
	}
	return ts
}

func (b *Builder) match(v *rules.Value) *Term {
	if v.IsLeaf() {
		if !v.IsVar() {
			return &Term{Sym: b.Syms.Fresh()}
		}
		s, _ := b.Rename(v.Name)
		if c := b.named[s]; c != nil {
			return c
		}
		return &Term{Sym: s}
	}
	t := &Term{Op: v.Op, Rest: v.Rest || v.Ellipsis}
	if v.Name != "" {
		t.Sym, _ = b.Rename(v.Name)
		if t.Sym == "" {
			t.Sym = b.Syms.Fresh()
		}
		b.named[t.Sym] = t
	} else {
		t.Sym = b.Syms.Fresh()
	}
	t.Type = b.Field(v.Type)
	t.AuxInt = b.Field(v.AuxInt)
	t.Aux = b.Field(v.Aux)
	for _, a := range v.Args {
		t.Args = append(t.Args, b.match(a))
	}
	return t
}

// Field returns the field for the text of a match's <type>, [auxint], or
// {aux}.
func (b *Builder) Field(text string) Field {
	switch {
	case text == "" || text == "_":
		return Field{Sym: b.Syms.Fresh()}
	case rules.IsVarText(text):
		s, _ := b.Rename(text)
		return Field{Sym: s}
	}
	return Field{Expr: Fold(Subst(text, b.Rename))}
}

// A Binding maps a pattern's variables to the terms and fields they match.
// Bindings are immutable.
type Binding struct {
	vals   map[string]*Term
	fields map[string]Field
}

func (b Binding) withVal(name string, t *Term) Binding {
	vals := maps.Clone(b.vals)
	if vals == nil {
		vals = map[string]*Term{}
	}
	vals[name] = t
	return Binding{vals, b.fields}
}

func (b Binding) withField(name string, f Field) Binding {
	fields := maps.Clone(b.fields)
	if fields == nil {
		fields = map[string]Field{}
	}
	fields[name] = f
	return Binding{b.vals, fields}
}

// Val returns the term bound to name.
func (b Binding) Val(name string) *Term { return b.vals[name] }

// Lookup returns the symbol or expression that name is bound to.
func (b Binding) Lookup(name string) (string, bool) {
	if t, ok := b.vals[name]; ok {
		return t.Sym, true
	}
	if f, ok := b.fields[name]; ok {
		return f.String(), true
	}
	return "", false
}

// Translate returns Go expression s, written in terms of the pattern's
// variables, in terms of the symbols they are bound to. extra gives
// bindings for other names, such as v.
func (b Binding) Translate(s string, extra map[string]string) string {
	return Subst(s, func(name string) (string, bool) {
		if r, ok := b.Lookup(name); ok {
			return r, true
		}
		r, ok := extra[name]
		return r, ok
	})
}

// Same reports whether terms a and b are certainly the same value.
func Same(a, b *Term) bool {
	return a == b || a.Sym != "" && a.Sym == b.Sym
}

// SameField reports whether fields a and b certainly have the same value.
func SameField(a, b Field) bool {
	if a.Sym != "" || b.Sym != "" {
		return a.Sym == b.Sym
	}
	return SameExpr(a.Expr, b.Expr)
}

// MatchValue calls k with each binding (extending b) under which pattern
// p certainly matches t, in the order rulegen's matcher tries them, until
// k returns true. It reports whether k returned true.
//
// p certainly matches t if it matches every value that t describes:
// t's leaves and field symbols are unknown, so p must not constrain them,
// except by binding them to variables.
func MatchValue(p *rules.Value, t *Term, b Binding, k func(Binding) bool) bool {
	if p.IsLeaf() {
		if !p.IsVar() {
			return k(b)
		}
		return bindVal(p.Name, t, b, k)
	}
	if t.Op == nil || t.Op != p.Op {
		return false
	}
	match := func(b Binding) bool {
		return MatchField(p.Type, t.Type, b, func(b Binding) bool {
			return MatchField(p.AuxInt, t.AuxInt, b, func(b Binding) bool {
				return MatchField(p.Aux, t.Aux, b, func(b Binding) bool {
					return matchArgs(p, t, b, k)
				})
			})
		})
	}
	if p.Name != "" {
		return bindVal(p.Name, t, b, match)
	}
	return match(b)
}

func matchArgs(p *rules.Value, t *Term, b Binding, k func(Binding) bool) bool {
	if p.Ellipsis {
		return k(b)
	}
	switch {
	case p.Rest:
		if len(t.Args) < len(p.Args) {
			return false
		}
	case t.Rest || len(t.Args) != len(p.Args):
		return false
	}
	args := t.Args
	if MatchValues(p.Args, args[:len(p.Args)], b, k) {
		return true
	}
	if p.Commutes() {
		swapped := append([]*Term{args[1], args[0]}, args[2:]...)
		return MatchValues(p.Args, swapped[:len(p.Args)], b, k)
	}
	return false
}

// MatchValues is like MatchValue for corresponding lists of patterns and
// terms.
func MatchValues(ps []*rules.Value, ts []*Term, b Binding, k func(Binding) bool) bool {
	if len(ps) == 0 {
		return k(b)
	}
	return MatchValue(ps[0], ts[0], b, func(b Binding) bool {
		return MatchValues(ps[1:], ts[1:], b, k)
	})
}

func bindVal(name string, t *Term, b Binding, k func(Binding) bool) bool {
	if old, ok := b.vals[name]; ok {
		return Same(old, t) && k(b)
	}
	return k(b.withVal(name, t))
}

// MatchField is like MatchValue for the text of a pattern's <type>,
// [auxint], or {aux} and a term's field.
func MatchField(text string, f Field, b Binding, k func(Binding) bool) bool {
	switch {
	case text == "" || text == "_":
		return k(b)
	case rules.IsVarText(text):
		if old, ok := b.fields[text]; ok {
			return SameField(old, f) && k(b)
		}
		return k(b.withField(text, f))
	}
	if f.Expr == "" {
		return false
	}
	return SameExpr(b.Translate(text, nil), f.Expr) && k(b)
}

// Fires reports whether value rule r certainly fires on t given facts:
// r's match certainly matches t, and r's condition is implied by facts.
// root is the symbol for v in r's condition (normally t.Sym).
func Fires(r *rules.Rule, t *Term, facts *Facts) bool {
	if r.IsBlock() {
		return false
	}
	conj := Conjuncts(r.Cond)
	extra := map[string]string{"v": t.Sym}
	return MatchValue(r.Match, t, Binding{}, func(b Binding) bool {
		for _, c := range conj {
			if !facts.Implies(b.Translate(c, extra)) {
				return false
			}
		}
		return true
	})
}
