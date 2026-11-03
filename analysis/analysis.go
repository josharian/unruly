// Package analysis is a minimal framework for static analyzers of SSA
// rewrite rules, in the spirit of golang.org/x/tools/go/analysis.
package analysis

import (
	"cmp"
	"errors"
	"fmt"
	"iter"
	"slices"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// An Analyzer is a static check of rules.
type Analyzer struct {
	Name string // a short identifier, such as "shadow"
	Doc  string // the first line is a one-sentence summary
	Run  func(*Pass) error
}

// A Pass provides an Analyzer with the rules to analyze and a way to
// report diagnostics. One Pass covers all selected rule sets.
type Pass struct {
	Analyzer *Analyzer
	Corpus   *rules.Corpus    // everything loaded
	Ops      *ops.Tables      // == Corpus.Ops
	Sets     []*rules.RuleSet // the rule sets to analyze, a subset of Corpus.Sets

	diags []Diagnostic
}

// Rules iterates over the rules of p.Sets, in order.
func (p *Pass) Rules() iter.Seq[*rules.Rule] {
	return func(yield func(*rules.Rule) bool) {
		for _, s := range p.Sets {
			for _, r := range s.Rules {
				if !yield(r) {
					return
				}
			}
		}
	}
}

// Report reports a diagnostic at pos.
func (p *Pass) Report(pos rules.Pos, msg string) {
	p.diags = append(p.diags, Diagnostic{Pos: pos, Analyzer: p.Analyzer.Name, Message: msg})
}

// Reportf reports a formatted diagnostic at pos.
func (p *Pass) Reportf(pos rules.Pos, format string, args ...any) {
	p.Report(pos, fmt.Sprintf(format, args...))
}

// A Diagnostic is a finding of an analyzer.
type Diagnostic struct {
	Pos      rules.Pos
	Analyzer string
	Message  string
}

func (d Diagnostic) String() string {
	return fmt.Sprintf("%s: %s: %s", d.Pos, d.Analyzer, d.Message)
}

// Run runs each analyzer over sets, which must belong to c.
// It returns the diagnostics sorted by position, with exact duplicates
// (such as from the | expansions of a single source rule) removed.
func Run(c *rules.Corpus, sets []*rules.RuleSet, analyzers []*Analyzer) ([]Diagnostic, error) {
	var diags []Diagnostic
	var errs []error
	for _, a := range analyzers {
		p := &Pass{Analyzer: a, Corpus: c, Ops: c.Ops, Sets: sets}
		if err := a.Run(p); err != nil {
			errs = append(errs, fmt.Errorf("%s: %v", a.Name, err))
		}
		diags = append(diags, p.diags...)
	}
	slices.SortFunc(diags, func(a, b Diagnostic) int {
		return cmp.Or(
			cmp.Compare(a.Pos.File, b.Pos.File),
			cmp.Compare(a.Pos.Line, b.Pos.Line),
			cmp.Compare(a.Analyzer, b.Analyzer),
			cmp.Compare(a.Message, b.Message),
		)
	})
	return slices.Compact(diags), errors.Join(errs...)
}
