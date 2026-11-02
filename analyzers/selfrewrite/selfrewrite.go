// Package selfrewrite reports rules that rewrite a value or block to itself.
package selfrewrite

import (
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "selfrewrite",
	Doc: `report unconditional rules whose result is identical to their match

Such a rule's result matches the rule again, so the rewrite loop never
terminates once the rule fires. (With a condition, such a rule can be a
legitimate way to reset a value's type or aux fields, so only rules
without conditions are reported.)`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for r := range pass.Rules() {
		if r.Cond != "" || r.Placement != "" || r.ResultCode != "" {
			continue
		}
		if same(r) {
			pass.Reportf(r.Pos, "result is identical to match; rewriting would never terminate")
		}
	}
	return nil
}

func same(r *rules.Rule) bool {
	if !r.IsBlock() {
		return !r.Result.IsLeaf() && text(r.Match) == text(r.Result)
	}
	m, res := r.MatchBlock, r.ResultBlock
	if m.Info != res.Info || m.AuxInt != res.AuxInt || m.Aux != res.Aux || len(m.Controls) != len(res.Controls) {
		return false
	}
	for i := range m.Controls {
		if text(m.Controls[i]) != text(res.Controls[i]) {
			return false
		}
	}
	return strings.Join(m.Succs, " ") == strings.Join(res.Succs, " ")
}

// text formats v without binding names, which don't affect what is
// matched or produced.
func text(v *rules.Value) string {
	if v.IsLeaf() {
		return v.Name
	}
	var b strings.Builder
	b.WriteString("(" + v.Op.QualifiedName() + " <" + v.Type + "> [" + v.AuxInt + "] {" + v.Aux + "}")
	for _, a := range v.Args {
		b.WriteString(" " + text(a))
	}
	if v.Ellipsis {
		b.WriteString(" ...")
	}
	if v.Rest {
		b.WriteString(" ___")
	}
	b.WriteString(")")
	return b.String()
}
