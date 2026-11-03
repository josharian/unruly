package loweringcoverage

import (
	"fmt"
	"go/ast"
	"go/parser"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// A term is a concrete SSA value tree that rules are matched against.
// A term with a nil op is an opaque value that matching cannot see into.
type term struct {
	op     *ops.Op
	typ    *typ // nil if unknown
	auxint val
	aux    val
	args   []*term
}

func (t *term) String() string {
	if t.op == nil {
		return "?"
	}
	var b strings.Builder
	b.WriteString("(" + t.op.Name)
	if t.auxint.k == vInt && t.op.HasAuxInt {
		fmt.Fprintf(&b, " [%d]", t.auxint.i)
	}
	if t.aux.k == vType && t.op.HasAux {
		fmt.Fprintf(&b, " {%s}", t.aux.t)
	}
	for _, a := range t.args {
		b.WriteString(" " + a.String())
	}
	b.WriteString(")")
	return b.String()
}

type archInfo struct {
	arch    *ops.Arch
	ptrSize int64
}

// matcher matches rules of one rule set against terms.
type matcher struct {
	arch *archInfo
	set  *rules.RuleSet
	tc   *typecheck.Result // nil if type checking failed
}

func newMatcher(ai *archInfo, set *rules.RuleSet) *matcher {
	m := &matcher{arch: ai, set: set}
	if res, err := typecheck.Check(set); err == nil {
		m.tc = res
	}
	return m
}

func (m *matcher) newEnv(knobs map[string]int64) *env {
	e := &env{arch: m.arch, vars: map[string]val{}, knobs: knobs}
	if m.tc != nil {
		e.info = m.tc.Info
	}
	return e
}

// expr returns the Go expression for field f of node v in rule r, or nil.
func (m *matcher) expr(r *rules.Rule, v *rules.Value, f typecheck.Field, text string) ast.Expr {
	if m.tc != nil {
		if tr := m.tc.Rule(r); tr != nil {
			if x := tr.Expr(v, f); x != nil {
				return x
			}
		}
	}
	x, err := parser.ParseExpr(text)
	if err != nil {
		return nil
	}
	return x
}

func (m *matcher) cond(r *rules.Rule) ast.Expr {
	if m.tc != nil {
		if tr := m.tc.Rule(r); tr != nil && tr.Cond != nil {
			return tr.Cond
		}
	}
	return r.CondExpr
}

// apply reports whether rule r applies to t: yes, no, or maybe (when the
// match or condition depends on something not modeled). Unless the
// answer is no, it also returns the environment of the match, which for
// maybe may lack some bindings.
func (m *matcher) apply(r *rules.Rule, t *term, knobs map[string]int64) (tri, *env) {
	if r.IsBlock() {
		return no, nil
	}
	if r.Match.Ellipsis {
		if t.op != r.Match.Op {
			return no, nil
		}
		e := m.newEnv(knobs)
		e.bind("v", termVal(t))
		return m.checkCond(r, e), e
	}
	for _, mv := range rules.Commutations(r.Match) {
		e := m.newEnv(knobs)
		e.bind("v", termVal(t))
		res := m.match(r, mv, t, e)
		if res != no {
			res = min3(res, m.checkCond(r, e))
		}
		if res != no {
			return res, e
		}
	}
	return no, nil
}

func (m *matcher) checkCond(r *rules.Rule, e *env) tri {
	c := m.cond(r)
	if c == nil {
		return yes
	}
	return e.eval(c).tri()
}

// match matches pattern p (one commutation of r's match, not commuting
// further) against t, binding variables in e.
func (m *matcher) match(r *rules.Rule, p *rules.Value, t *term, e *env) tri {
	if p.IsLeaf() {
		return m.bindOrCompare(p.Name, termVal(t), e)
	}
	if t.op == nil {
		return maybe
	}
	if p.Op != t.op {
		return no
	}
	if p.Name != "" {
		if res := m.bindOrCompare(p.Name, termVal(t), e); res != yes {
			return res
		}
	}
	if p.Rest {
		if len(t.args) < len(p.Args) {
			return no
		}
	} else if len(t.args) != len(p.Args) {
		return no
	}
	res := yes
	fields := []struct {
		text string
		f    typecheck.Field
		v    val
	}{
		{p.Type, typecheck.Type, typValOrUnknown(t.typ)},
		{p.AuxInt, typecheck.AuxInt, t.auxint},
		{p.Aux, typecheck.Aux, t.aux},
	}
	for _, f := range fields {
		switch {
		case f.text == "" || f.text == "_":
		case rules.IsVarText(f.text):
			res = min3(res, m.bindOrCompare(f.text, f.v, e))
		default:
			x := m.expr(r, p, f.f, f.text)
			if x == nil {
				res = min3(res, maybe)
				continue
			}
			res = min3(res, equal(e.eval(x), f.v).tri())
		}
		if res == no {
			return no
		}
	}
	for i, a := range p.Args {
		res = min3(res, m.match(r, a, t.args[i], e))
		if res == no {
			return no
		}
	}
	return res
}

// min3 is three-valued conjunction.
func min3(a, b tri) tri {
	if a == no || b == no {
		return no
	}
	if a == maybe || b == maybe {
		return maybe
	}
	return yes
}

func typValOrUnknown(t *typ) val {
	if t == nil {
		return unknown
	}
	return typVal(t)
}

func (m *matcher) bindOrCompare(name string, v val, e *env) tri {
	if name == "_" {
		return yes
	}
	if old, ok := e.vars[name]; ok {
		return equal(old, v).tri()
	}
	e.bind(name, v)
	return yes
}

// build constructs the result of rule r, which matched t with environment e.
// It returns nil if the result is not modeled.
func (m *matcher) build(r *rules.Rule, t *term, e *env) *term {
	if r.Result == nil {
		return nil
	}
	if r.Match.Ellipsis {
		nt := *t
		nt.op = r.Result.Op
		return &nt
	}
	shared := map[string]*term{}
	var build func(v *rules.Value) *term
	build = func(v *rules.Value) *term {
		if v.IsLeaf() {
			if b, ok := e.vars[v.Name]; ok && b.k == vTerm {
				return b.term
			}
			return &term{} // opaque
		}
		if s, ok := shared[v.Text]; ok {
			return s
		}
		nt := &term{op: v.Op, auxint: intVal(0), aux: val{k: vNil}}
		switch typText, src := r.ResultType(v); src {
		case rules.TypeExplicit:
			if x := m.expr(r, v, typecheck.Type, typText); x != nil {
				if tv := e.eval(x); tv.k == vType {
					nt.typ = tv.t
				}
			}
		case rules.TypeOpDefault:
			if x, err := parser.ParseExpr(ops.TypeExpr(typText)); err == nil {
				if tv := e.eval(x); tv.k == vType {
					nt.typ = tv.t
				}
			}
		case rules.TypeInherited:
			nt.typ = t.typ
		}
		if v.AuxInt != "" {
			nt.auxint = unknown
			if x := m.expr(r, v, typecheck.AuxInt, v.AuxInt); x != nil {
				nt.auxint = e.eval(x)
			}
		}
		if v.Aux != "" {
			nt.aux = unknown
			if x := m.expr(r, v, typecheck.Aux, v.Aux); x != nil {
				nt.aux = e.eval(x)
			}
		}
		for _, a := range v.Args {
			nt.args = append(nt.args, build(a))
		}
		shared[v.Text] = nt
		return nt
	}
	return build(r.Result)
}

// rewrite returns the normal forms of t under the rule sets, applied in
// order (as the lower and late lower passes are). Where a rule may or may
// not apply, it follows both possibilities. It returns nil if there are
// too many possibilities to follow.
func rewrite(t *term, sets []*matcher) []*term {
	ts := []*term{t}
	for _, m := range sets {
		var next []*term
		for _, t := range ts {
			next = append(next, m.normalize(t, 0)...)
		}
		if len(next) == 0 || len(next) > maxOutcomes {
			return nil
		}
		ts = next
	}
	return ts
}

const (
	maxDepth    = 20
	maxOutcomes = 16
)

// normalize returns the possible normal forms of t, or nil if there are
// too many.
func (m *matcher) normalize(t *term, depth int) []*term {
	if t.op == nil {
		return []*term{t}
	}
	if depth > maxDepth {
		return nil
	}
	// Normalize the arguments, then the root.
	alts := []*term{t}
	for i := range t.args {
		var next []*term
		for _, alt := range alts {
			for _, na := range m.normalize(alt.args[i], depth+1) {
				nt := *alt
				nt.args = append([]*term(nil), alt.args...)
				nt.args[i] = na
				next = append(next, &nt)
			}
		}
		if len(next) == 0 || len(next) > maxOutcomes {
			return nil
		}
		alts = next
	}
	var res []*term
	for _, alt := range alts {
		res = append(res, m.normalizeRoot(alt, depth)...)
		if len(res) > maxOutcomes {
			return nil
		}
	}
	return res
}

// normalizeRoot rewrites t, whose args are normalized, at its root.
func (m *matcher) normalizeRoot(t *term, depth int) []*term {
	var res []*term
	for _, r := range m.set.ByOp[t.op] {
		ok, e := m.apply(r, t, nil)
		if ok == no {
			continue
		}
		nt := m.build(r, t, e)
		if nt == nil {
			return nil
		}
		next := m.normalize(nt, depth+1)
		if next == nil {
			return nil
		}
		res = append(res, next...)
		if ok == yes {
			return res
		}
		// The rule may not apply; consider the remaining rules too.
	}
	return append(res, t)
}
