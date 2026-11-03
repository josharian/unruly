// Package rewritecycle reports rules that rewrite a value back and forth
// forever.
package rewritecycle

import (
	"fmt"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/shadow/term"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "rewritecycle",
	Doc: `report rules that rewrite a value into a form they (or a partner) rewrite back

The rewrite pass applies rules until nothing changes. If a rule's result
matches the rule again, or a second rule's match, whose result in turn
matches the first rule, the pass never terminates and the compiler dies
with "rewrite cycle detected" (or, in older compilers, hangs). For
example, with

	(TESTQconst [-1] x) => (TESTQ x x)
	(TESTQ (MOVQconst [c]) x) && is32Bit(c) => (TESTQconst [c] x)

the value (TESTQconst [-1] (MOVQconst [-1])) becomes
(TESTQ (MOVQconst [-1]) (MOVQconst [-1])) and then the original again
(go.dev/issue/25006). The fix is a guard such as x.Op != OpAMD64MOVQconst.

For each rule A, the analyzer instantiates A's result and unifies it with
the match of each rule B for the result's op, refining A's variables as
needed (here, x := (MOVQconst [c])). It reports a cycle if B's result is
then A's match again (or, for B = A, A's result again), no earlier rule
certainly fires first on either value, and the conditions of A and B are
not contradictory. Conditions are assumed satisfiable unless the analyzer
can refute them: x.Op != OpFoo when x is a Foo, constant conditions,
integer bounds, a condition and its negation, and the strict order
CanonLessThan.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, s := range pass.Sets {
		reported := map[[2]*rules.Rule]bool{}
		for _, a := range s.Rules {
			if c := findCycle(s, a); c != nil {
				key := [2]*rules.Rule{a, c.b}
				if before(c.b, a) {
					key = [2]*rules.Rule{c.b, a}
				}
				if reported[key] {
					continue
				}
				reported[key] = true
				pass.Report(a.Pos, c.message(a))
			}
		}
	}
	return nil
}

func before(a, b *rules.Rule) bool {
	if a.Pos.File != b.Pos.File {
		return a.Pos.File < b.Pos.File
	}
	return a.Pos.Line < b.Pos.Line || a.Pos.Line == b.Pos.Line && a.Alt < b.Alt
}

type cycle struct {
	b          *rules.Rule
	t0, t1, t2 *term.Term // the value before A, after A, after B
	self       bool       // B == A and t2 is t1 again
}

// show formats t for a message: a's variables keep their names,
// b's are primed, and wildcards are _.
func show(t *term.Term) string {
	s := strings.ReplaceAll(t.String(), "ǀ0", "")
	s = strings.ReplaceAll(s, "ǀ1", "'")
	return wildcard.ReplaceAllString(s, "_")
}

var wildcard = regexp.MustCompile(`τ[0-9]+`)

func (c *cycle) message(a *rules.Rule) string {
	if c.self {
		return fmt.Sprintf("rewrite cycle: this rule rewrites %s to %s, which it matches again, producing the same value forever", show(c.t0), show(c.t1))
	}
	if c.b == a {
		return fmt.Sprintf("rewrite cycle: this rule rewrites %s to %s, and then back to %s", show(c.t0), show(c.t1), show(c.t2))
	}
	return fmt.Sprintf("rewrite cycle: this rule rewrites %s to %s, which %s:%d (%s) rewrites back to %s",
		show(c.t0), show(c.t1), filepath.Base(c.b.Pos.File), c.b.Pos.Line, c.b.MatchText, show(c.t2))
}

// inst is an instance of a rule with its variables renamed apart.
type inst struct {
	r      *rules.Rule
	syms   *term.Symbols
	rename func(string) (string, bool)
	match  *term.Term
	bySym  map[string]*term.Term // match terms by symbol
}

func instantiate(r *rules.Rule, syms *term.Symbols, n int) *inst {
	vars := r.MatchVars()
	// ǀ (U+01C0) is a letter, so renamed variables are identifiers,
	// but it never appears in rules.
	suffix := fmt.Sprintf("ǀ%d", n)
	in := &inst{r: r, syms: syms, bySym: map[string]*term.Term{}}
	in.rename = func(name string) (string, bool) {
		if _, ok := vars[name]; ok {
			return name + suffix, true
		}
		return "", false
	}
	b := &term.Builder{Syms: syms, Rename: in.rename}
	in.match = b.Match(r.Match)[0]
	var walk func(t *term.Term)
	walk = func(t *term.Term) {
		if _, ok := in.bySym[t.Sym]; ok {
			return
		}
		in.bySym[t.Sym] = t
		for _, a := range t.Args {
			walk(a)
		}
	}
	walk(in.match)
	return in
}

// result builds the term that in's rule rewrites root (the value its match
// matched) to, or nil if it is not a compound value built from the match.
func (in *inst) result(root *term.Term) *term.Term {
	r := in.r
	if r.Result == nil || r.Result.IsLeaf() {
		return nil
	}
	shared := map[string]*term.Term{}
	var build func(v *rules.Value) *term.Term
	build = func(v *rules.Value) *term.Term {
		if v.IsLeaf() {
			if s, ok := in.rename(v.Name); ok {
				if t := in.bySym[s]; t != nil {
					return t
				}
			}
			return &term.Term{Sym: in.syms.Fresh(), Rigid: true}
		}
		top := v == r.Result
		if v.Ellipsis {
			t := *root
			t.Op = v.Op
			return &t
		}
		if !top {
			if t, ok := shared[v.Text]; ok {
				return t
			}
		}
		t := &term.Term{Op: v.Op, Sym: in.syms.Fresh()}
		if top && r.Placement == "" {
			t.Sym = root.Sym
		}
		switch typ, src := r.ResultType(v); src {
		case rules.TypeExplicit:
			t.Type = in.field(typ)
		case rules.TypeOpDefault:
			t.Type = term.Field{Expr: term.Canon(ops.TypeExpr(typ))}
		case rules.TypeInherited:
			t.Type = root.Type
		}
		switch {
		case v.AuxInt != "":
			t.AuxInt = in.field(v.AuxInt)
		case v.Op.HasAuxInt:
			t.AuxInt = term.Field{Expr: "0"}
		}
		switch {
		case v.Aux != "":
			t.Aux = in.field(v.Aux)
		case v.Op.HasAux:
			t.Aux = term.Field{Expr: "nil"}
		}
		for _, a := range v.Args {
			t.Args = append(t.Args, build(a))
		}
		if !top {
			shared[v.Text] = t
		}
		return t
	}
	return build(r.Result)
}

// field converts a result's Go expression to a field.
func (in *inst) field(text string) term.Field {
	if sym, ok := in.rename(text); ok && in.bySym[sym] == nil {
		return term.Field{Sym: sym} // a type, auxint, or aux variable
	}
	return term.Field{Expr: term.Fold(term.Subst(text, in.rename))}
}

// conds returns in's condition conjuncts in terms of its symbols,
// with v standing for root.
func (in *inst) conds(root string) []string {
	var out []string
	for _, c := range term.Conjuncts(in.r.Cond) {
		out = append(out, term.Subst(c, func(name string) (string, bool) {
			if name == "v" {
				return root, true
			}
			return in.rename(name)
		}))
	}
	return out
}

func rewrites(r *rules.Rule) bool {
	return !r.IsBlock() && r.Result != nil && !r.Result.IsLeaf()
}

// findCycle returns a cycle starting with rule a, or nil.
func findCycle(set *rules.RuleSet, a *rules.Rule) *cycle {
	if !rewrites(a) {
		return nil
	}
	syms := new(term.Symbols)
	ia := instantiate(a, syms, 0)
	t0 := ia.match
	t1 := ia.result(t0)
	if t1 == nil {
		return nil
	}
	var found *cycle
	for _, b := range set.ByOp[t1.Op] {
		if !rewrites(b) {
			continue
		}
		ib := instantiate(b, syms, 1)
		unify(ib.match, t1, subst{}, func(s subst) bool {
			t2 := ib.result(t1)
			if t2 == nil {
				return false
			}
			// Does B's result close the cycle: is it A's match again
			// (or, for B = A, A's result again)?
			// Types count only if a condition looks at them: a rule
			// may legitimately rewrite a value to itself to change
			// its type, with a condition that then fails. If so,
			// the type must certainly never change.
			if (mentionsType(a) || mentionsType(b)) &&
				!(sameField(t0.Type, t1.Type, s) && sameField(t1.Type, t2.Type, s)) {
				return false
			}
			try := func(back *term.Term, self bool) bool {
				return unifyTyped(back, t2, s, false, func(s subst) bool {
					c := &cycle{b: b, self: self}
					c.t0, c.t1, c.t2 = s.apply(t0), s.apply(t1), s.apply(t2)
					if !feasible(set, ia, ib, c, s) {
						return false
					}
					found = c
					return true
				})
			}
			return try(t0, false) || b == a && try(t1, true)
		})
		if found != nil {
			return found
		}
	}
	return nil
}

// feasible reports whether the cycle c can happen: the conditions of
// both rules can hold, no earlier rule certainly fires first, and the
// rule to apply next matches the final value again.
func feasible(set *rules.RuleSet, ia, ib *inst, c *cycle, s subst) bool {
	facts := term.NewFacts()
	facts.UseHelpers(set.Arch.Tables().Dir)
	facts.AddTerm(c.t0)
	facts.AddTerm(c.t1)
	facts.AddTerm(c.t2)
	var conds []string
	for _, x := range ia.conds(c.t0.Sym) {
		conds = append(conds, s.text(x))
	}
	for _, x := range ib.conds(c.t1.Sym) {
		conds = append(conds, s.text(x))
	}
	for _, x := range conds {
		if facts.Refutes(x) {
			return false
		}
		facts.Assume(x)
	}
	for _, x := range conds {
		if facts.Refutes(x) {
			return false
		}
	}
	if preempted(set, ia.r, c.t0, facts) || preempted(set, ib.r, c.t1, facts) {
		return false
	}
	// The rule that applies next must match the final value again.
	next, val := ia.r, c.t2
	if c.self {
		next = ib.r
	}
	if preempted(set, next, val, facts) {
		return false
	}
	conj := term.Conjuncts(next.Cond)
	return term.MatchValue(next.Match, val, term.Binding{}, func(b term.Binding) bool {
		for _, x := range conj {
			if facts.Refutes(b.Translate(x, map[string]string{"v": val.Sym})) {
				return false
			}
		}
		return true
	})
}

// preempted reports whether a rule before r certainly fires on t.
func preempted(set *rules.RuleSet, r *rules.Rule, t *term.Term, facts *term.Facts) bool {
	for _, e := range set.ByOp[t.Op] {
		if e == r {
			return false
		}
		if term.Fires(e, t, facts) {
			return true
		}
	}
	return false
}

// mentionsType reports whether r's condition looks at a type: a type
// variable of its match or a .Type field.
func mentionsType(r *rules.Rule) bool {
	if r.Cond == "" {
		return false
	}
	if strings.Contains(r.Cond, ".Type") {
		return true
	}
	for _, o := range r.MatchOccurrences() {
		if o.Kind == rules.OccType {
			for _, id := range term.Idents(r.Cond) {
				if id == o.Name {
					return true
				}
			}
		}
	}
	return false
}
