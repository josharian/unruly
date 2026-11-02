// Package dupmatch reports rules that are shadowed by an earlier,
// equivalent rule.
package dupmatch

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"path/filepath"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "dupmatch",
	Doc: `report rules shadowed by an earlier rule with an equivalent match and condition

Within a rule set, the first matching rule for an op wins, so a rule whose
match and condition are equivalent to an earlier rule's can never fire.
Equivalence allows renaming variables and swapping the arguments of
commutative ops. rulegen itself rejects only textually identical rules.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, s := range pass.Sets {
		seen := make(map[string]*rules.Rule)
		for _, r := range s.Rules {
			k := key(r)
			prev, ok := seen[k]
			if !ok {
				seen[k] = r
				continue
			}
			if prev.Pos == r.Pos {
				continue // two expansions of one source rule
			}
			pass.Reportf(r.Pos, "rule is shadowed by equivalent rule at %s:%d", filepath.Base(prev.Pos.File), prev.Pos.Line)
		}
	}
	return nil
}

// key returns a canonical form of r's match and condition: the least,
// over all commutations of the match, of the match and condition with
// variables renamed in order of first appearance.
func key(r *rules.Rule) string {
	uses := useCounts(r)
	var variants [][]*rules.Value
	if r.IsBlock() {
		variants = [][]*rules.Value{nil}
		for _, c := range r.MatchBlock.Controls {
			var next [][]*rules.Value
			for _, prefix := range variants {
				for _, cv := range rules.Commutations(c) {
					next = append(next, append(prefix[:len(prefix):len(prefix)], cv))
				}
			}
			variants = next
		}
	} else {
		for _, v := range rules.Commutations(r.Match) {
			variants = append(variants, []*rules.Value{v})
		}
	}
	best := ""
	for i, vals := range variants {
		c := &canon{uses: uses, names: make(map[string]string)}
		if r.IsBlock() {
			b := r.MatchBlock
			fmt.Fprintf(&c.buf, "(%s [%s] {%s} %d", b.Info.QualifiedName(), c.text(b.AuxInt), c.text(b.Aux), len(b.Succs))
		}
		for _, v := range vals {
			c.value(v)
		}
		c.buf.WriteString(" && ")
		c.buf.WriteString(c.expr(r.Cond))
		if s := c.buf.String(); i == 0 || s < best {
			best = s
		}
	}
	return best
}

// useCounts counts the occurrences of each match variable in r's match
// and condition. A variable used once matches anything.
func useCounts(r *rules.Rule) map[string]int {
	uses := make(map[string]int)
	for _, o := range r.MatchOccurrences() {
		uses[o.Name]++
	}
	if r.CondExpr != nil {
		ast.Inspect(r.CondExpr, func(n ast.Node) bool {
			if id, ok := n.(*ast.Ident); ok && uses[id.Name] > 0 {
				uses[id.Name]++
			}
			return true
		})
	}
	return uses
}

type canon struct {
	uses  map[string]int
	names map[string]string
	buf   bytes.Buffer
}

func (c *canon) name(s string) string {
	if n, ok := c.names[s]; ok {
		return n
	}
	n := fmt.Sprintf("v%d", len(c.names))
	c.names[s] = n
	return n
}

// text canonicalizes the contents of <>, [], or {} in a match.
func (c *canon) text(s string) string {
	if rules.IsVarText(s) {
		if c.uses[s] <= 1 {
			return ""
		}
		return c.name(s)
	}
	return c.expr(s)
}

func (c *canon) value(v *rules.Value) {
	if v.IsLeaf() {
		if v.IsVar() && c.uses[v.Name] > 1 {
			c.buf.WriteString(" " + c.name(v.Name))
		} else {
			c.buf.WriteString(" _")
		}
		return
	}
	c.buf.WriteString(" ")
	if v.Name != "" && c.uses[v.Name] > 1 {
		c.buf.WriteString(c.name(v.Name) + ":")
	}
	fmt.Fprintf(&c.buf, "(%s <%s> [%s] {%s}", v.Op.QualifiedName(), c.text(v.Type), c.text(v.AuxInt), c.text(v.Aux))
	for _, a := range v.Args {
		c.value(a)
	}
	if v.Ellipsis {
		c.buf.WriteString(" ...")
	}
	if v.Rest {
		c.buf.WriteString(" ___")
	}
	c.buf.WriteString(")")
}

// expr canonicalizes Go expression s, renaming match variables.
func (c *canon) expr(s string) string {
	if s == "" {
		return ""
	}
	x, err := parser.ParseExpr(s)
	if err != nil {
		return strings.Join(strings.Fields(s), " ")
	}
	// Rename identifiers, but not field and method names.
	var walk func(n ast.Node) bool
	walk = func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.SelectorExpr:
			ast.Inspect(n.X, walk)
			return false
		case *ast.KeyValueExpr:
			ast.Inspect(n.Value, walk)
			return false
		case *ast.Ident:
			if c.uses[n.Name] > 0 {
				n.Name = c.name(n.Name)
			}
		}
		return true
	}
	ast.Inspect(x, walk)
	var buf bytes.Buffer
	printer.Fprint(&buf, token.NewFileSet(), x)
	return buf.String()
}
