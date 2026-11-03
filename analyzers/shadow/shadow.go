// Package shadow reports rules that can never fire because an earlier
// rule always fires first.
package shadow

import (
	"fmt"
	"go/scanner"
	"go/token"
	"path/filepath"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/shadow/term"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "shadow",
	Doc: `report rules shadowed by an earlier rule that always fires first

Within a rule set, rulegen tries the rules for an op in order, and the
first whose match and condition succeed wins. A later rule is dead if an
earlier rule matches every value it matches, whenever its condition holds.
For example, in ARM64.rules

	((EQ|NE) (CMPconst [0] x) yes no) => ((Z|NZ) x yes no)
	...
	((EQ|NE) (CMPconst [0] z:(MADD a x y)) yes no) && z.Uses==1 => ...

the second rule never fires for EQ and NE. Dead rules are usually a typo
for the rule that was intended (an op or argument copied from the
neighboring rule) or an optimization that silently does nothing.

The earlier rule shadows the later one if its match is at least as
general (its variables may bind to subexpressions of the later match;
repeated variables must bind to the same value; literal auxints must
agree; commutative ops match either way) and each conjunct of its
condition, after renaming, is implied by the later rule: it is one of
the later rule's conjuncts, follows from the later rule's integer bounds
(rc <= 31 implies rc < 32) or match (x.Op != OpConst64 when x is an
Add64), is constant, or is a helper like Clobber that always returns
true.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, s := range pass.Sets {
		for _, group := range s.ByOp {
			check(pass, group)
		}
		for _, group := range s.ByBlock {
			check(pass, group)
		}
	}
	return nil
}

func check(pass *analysis.Pass, group []*rules.Rule) {
	for j, r := range group {
		if r.IsBlock() && r.MatchBlock == nil || !r.IsBlock() && r.Match == nil {
			continue
		}
		t := newTarget(r)
		for _, prev := range group[:j] {
			if b, ok := t.shadowedBy(prev); ok {
				report(pass, r, prev, b)
				break
			}
		}
	}
}

func report(pass *analysis.Pass, r, prev *rules.Rule, b term.Binding) {
	where := fmt.Sprintf("%s:%d", filepath.Base(prev.Pos.File), prev.Pos.Line)
	if prev.Pos == r.Pos {
		where = "another expansion of the same rule"
	}
	shadow := prev.MatchText
	if prev.Cond != "" {
		shadow += " && " + prev.Cond
	}
	what := r.MatchText
	if r.NumAlts > 1 {
		what = "expansion " + what
	}
	msg := fmt.Sprintf("rule %s never fires: %s, %s, matches first", what, where, shadow)
	if sameResult(r, prev, b) {
		msg += " (with the same result)"
	}
	pass.Report(r.Pos, msg)
}

// target is a rule whose match is converted to terms, to see whether an
// earlier rule matches it.
type target struct {
	r      *rules.Rule
	ts     []*term.Term // the match value or block controls
	auxInt term.Field   // block fields
	aux    term.Field
	facts  *term.Facts
	root   string // symbol for v
}

func newTarget(r *rules.Rule) *target {
	vars := r.MatchVars()
	rootName := ""
	if !r.IsBlock() {
		rootName = r.Match.Name
	}
	rename := func(name string) (string, bool) {
		if _, ok := vars[name]; !ok {
			return "", false
		}
		if name == rootName {
			return "v", true
		}
		return name, true
	}
	b := &term.Builder{Syms: new(term.Symbols), Rename: rename}
	t := &target{r: r, facts: term.NewFacts()}
	t.facts.UseHelpers(r.Set.Arch.Tables().Dir)
	if r.IsBlock() {
		t.ts = b.Match(r.MatchBlock.Controls...)
		t.auxInt = b.Field(r.MatchBlock.AuxInt)
		t.aux = b.Field(r.MatchBlock.Aux)
	} else {
		t.ts = b.Match(r.Match)
		if rootName == "" {
			t.ts[0].Sym = "v"
		}
		t.root = t.ts[0].Sym
	}
	for _, x := range t.ts {
		t.facts.AddTerm(x)
	}
	t.facts.Assume(term.Subst(r.Cond, rename))
	return t
}

// shadowedBy reports whether p fires whenever t.r would,
// and if so, the binding of p's variables.
func (t *target) shadowedBy(p *rules.Rule) (term.Binding, bool) {
	conj := term.Conjuncts(p.Cond)
	var found term.Binding
	implied := func(b term.Binding) bool {
		extra := map[string]string{}
		if t.root != "" {
			extra["v"] = t.root
		}
		for _, c := range conj {
			if !t.facts.Implies(b.Translate(c, extra)) {
				return false
			}
		}
		found = b
		return true
	}
	if !p.IsBlock() {
		ok := term.MatchValue(p.Match, t.ts[0], term.Binding{}, implied)
		return found, ok
	}
	pb := p.MatchBlock
	ok := term.MatchField(pb.AuxInt, t.auxInt, term.Binding{}, func(b term.Binding) bool {
		return term.MatchField(pb.Aux, t.aux, b, func(b term.Binding) bool {
			return term.MatchValues(pb.Controls, t.ts, b, implied)
		})
	})
	return found, ok
}

// sameResult reports whether prev's result, with its variables renamed to
// what they bind in r, is textually identical to r's, as a hint that the
// dead rule is merely redundant.
func sameResult(r, prev *rules.Rule, b term.Binding) bool {
	if r.IsBlock() {
		// Successor names are not variables of the match.
		return false
	}
	ok := true
	got := tokens(prev.ResultText, func(name string) string {
		if name == "v" {
			return name
		}
		s, bound := b.Lookup(name)
		if !bound {
			return name
		}
		if strings.HasPrefix(s, "τ") {
			ok = false // bound to an unnamed part of r's match
		}
		return s
	})
	rootName := r.Match.Name
	want := tokens(r.ResultText, func(name string) string {
		if name == rootName {
			return "v"
		}
		return name
	})
	return ok && got == want
}

// tokens returns s with each identifier that is not a selector renamed
// by f, with one space between tokens.
func tokens(s string, f func(string) string) string {
	var sc scanner.Scanner
	fset := token.NewFileSet()
	sc.Init(fset.AddFile("", -1, len(s)), []byte(s), nil, 0)
	var out strings.Builder
	prev := token.ILLEGAL
	for {
		_, tok, lit := sc.Scan()
		if tok == token.EOF {
			break
		}
		text := lit
		if text == "" {
			text = tok.String()
		}
		if tok == token.IDENT && prev != token.PERIOD {
			text = f(lit)
		}
		out.WriteString(text + " ")
		prev = tok
	}
	return out.String()
}
