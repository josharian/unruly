// Package valuekind reports rules that change what kind of value an SSA
// value is: memory into a register value, a tuple into memory, flags into
// an integer, or an integer into a floating-point register.
package valuekind

import (
	"fmt"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "valuekind",
	Doc: `report rules whose result has a different kind or register class than the value it replaces

A rule's top-level result replaces the matched value in all of its uses,
and, unless it gives a type, keeps the matched value's type. So the
result op must produce the same kind of value: memory for memory, a
tuple for a tuple, flags for flags, a register value for a register
value. For example, before Go 1.23 the generic AtomicAnd8 was typed
(Uint8, Mem), and

	(AtomicAnd8 ptr val mem) => (ANDBlock ptr val mem)

replaced it with an op that produces only memory.

For a register value, the result op's output register must also suit the
value's type. Register allocation, spills, and phi moves choose registers
and instructions from the type, so

	(Cvt64Fto32 ...) => (TRUNCDW ...)

which leaves an integer-typed value in a floating-point register, made
loong64 spill a uint8 phi with an 8-byte MOVD (go.dev/issue/81000).

It also reports a <type> whose kind contradicts the op it annotates,
such as (MOVLconst <x.Type> [1]) where x is a flags value, and Select0
or Select1 of an op that does not produce a tuple.

Kinds come from the ops' default types and register outputs.
Polymorphic ops (Copy, Phi, Load, Select0, ...) and ops whose tables
don't determine a kind are not checked.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	f := newFacts(pass.Corpus)
	for r := range pass.Rules() {
		if r.IsBlock() || r.Result == nil {
			continue
		}
		c := &checker{env: newEnv(f, r), pass: pass}
		c.checkRoot()
		c.checkAnnotations()
		c.checkSelects()
	}
	return nil
}

type checker struct {
	*env
	pass     *analysis.Pass
	reported bool
}

func (c *checker) report(format string, args ...any) {
	if c.reported {
		return
	}
	c.reported = true
	c.pass.Reportf(c.r.Pos, format, args...)
}

// produced returns the shape of the value that result node n's op
// produces, regardless of the type the rule gives it.
func (c *checker) produced(n *rules.Value) shape {
	if n.IsLeaf() {
		return c.resultShape(n)
	}
	switch n.OpName {
	case "Select0", "Select1":
		if len(n.Args) != 1 {
			break
		}
		a := c.resultShape(n.Args[0])
		i := 0
		if n.OpName == "Select1" {
			i = 1
		}
		if a.kind == tuple && len(a.elems) == 2 {
			return a.elems[i]
		}
		return shape{}
	case "Copy":
		if len(n.Args) == 1 {
			return c.resultShape(n.Args[0])
		}
	case "Last":
		if len(n.Args) > 0 {
			return c.resultShape(n.Args[len(n.Args)-1])
		}
	}
	return c.f.intrinsic(n.Op)
}

// resultShape returns the shape of the type result node n gets.
func (c *checker) resultShape(n *rules.Value) shape {
	if n.IsLeaf() {
		if v := c.valueVar(n.Name); v != nil {
			return c.matchShape(v)
		}
		return shape{}
	}
	typ, src := c.r.ResultType(n)
	switch src {
	case rules.TypeExplicit:
		return c.exprShape(typ)
	case rules.TypeInherited:
		return c.matchShape(c.r.Match)
	case rules.TypeOpDefault:
		if typ != "" {
			return typeName(typ)
		}
	}
	return c.produced(n)
}

// checkRoot checks that the top-level result produces the same kind of
// value as the match, and for a register value, in a suitable register.
func (c *checker) checkRoot() {
	m := c.matchShape(c.r.Match)
	if !m.known() || m.kind == void {
		// A void value has no uses, so its replacement's kind is moot.
		return
	}
	res := c.r.Result
	mop := c.r.Match.OpName
	if res.IsLeaf() {
		s := c.resultShape(res)
		if s.known() && s.kind != m.kind {
			c.report("%s is %s, but the result %s is %s; it replaces %s in uses that expect %s",
				mop, m.describe(), res.Name, s.describe(), mop, m.kind)
		}
		return
	}
	typ, src := c.r.ResultType(res)
	if src != rules.TypeExplicit {
		p := c.produced(res)
		if p.known() && p.kind != m.kind {
			c.report("%s is %s, but %s produces %s; the result replaces it in uses that expect %s",
				mop, m.describe(), res.OpName, p.describe(), m.kind)
			return
		}
	}
	// Register class. The result's type is m's (inherited) or explicit.
	var want shape
	switch src {
	case rules.TypeInherited:
		want = m
	case rules.TypeExplicit:
		want = c.exprShape(typ)
	}
	if want.kind != value || want.class == anyClass {
		return
	}
	out := outClass(res.Op)
	if out == anyClass || out == want.class {
		return
	}
	what := "the result has " + mop + "'s type"
	if src == rules.TypeExplicit {
		what = "the result has type " + typ
	}
	c.report("%s writes %s register, but %s, which needs %s register; register allocation "+
		"and spills choose registers and instructions by type, so, for example, a uint8 phi of it "+
		"can be spilled with an 8-byte FP store (go.dev/issue/81000)",
		res.OpName, article(out), what, article(want.class))
}

func article(c class) string {
	if c == fp {
		return "a floating-point"
	}
	return "an integer"
}

// checkAnnotations checks that each explicit result <type> has the kind
// of value its op produces.
func (c *checker) checkAnnotations() {
	c.r.Result.Walk(func(n *rules.Value) bool {
		if n.IsLeaf() || n.Type == "" {
			return true
		}
		t := c.exprShape(n.Type)
		p := c.produced(n)
		if t.known() && p.known() && t.kind != p.kind {
			c.report("(%s <%s>) gives %s type to an op that produces %s", n.OpName, n.Type, kindNoun(t), p.describe())
			return false
		}
		return true
	})
}

func kindNoun(s shape) string {
	switch s.kind {
	case value:
		return "a value"
	case mem:
		return "a memory"
	case flags:
		return "a flags"
	case tuple:
		return "a tuple"
	}
	return fmt.Sprintf("a %s", s.kind)
}

// checkSelects checks that Select0 and Select1 select from tuples.
func (c *checker) checkSelects() {
	check := func(match bool) func(*rules.Value) bool {
		return func(n *rules.Value) bool {
			if n.IsLeaf() || (n.OpName != "Select0" && n.OpName != "Select1") || len(n.Args) != 1 {
				return true
			}
			a := n.Args[0]
			var s shape
			if match {
				s = c.matchShape(a)
			} else {
				s = c.resultShape(a)
			}
			if s.known() && s.kind != tuple {
				c.report("%s of %s, which is %s, not a tuple", n.OpName, a.Text, s.describe())
				return false
			}
			return true
		}
	}
	c.r.Match.Walk(check(true))
	c.r.Result.Walk(check(false))
}
