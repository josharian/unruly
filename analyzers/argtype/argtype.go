// Package argtype reports rules that decide what an op does from the
// types of its arguments rather than from the op itself.
package argtype

import (
	"fmt"
	"go/ast"
	"go/parser"
	"regexp"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "argtype",
	Doc: `report rules that rely on the type of an argument value

An SSA value's own type (v.Type, the root's <t>, a Store's {t}) says what
the value is. An argument's type says much less: conversions between
same-sized types and between pointer types are copies that copyelim
removes, and lowering turns truncations into copies, so an argument can
have any type of the right register shape. For example, after

	(Trunc32to16 ...) => (Copy ...)

the value stored by (Store {t} ptr val mem) with t 2 bytes wide can be a
4-byte val, and int8(u) of a uint8 u is u itself. This analyzer reports:

  - Store, Move, Zero, shift, and truncation rules whose condition
    reads the .Type of an argument. The width, float-ness, or signedness
    must come from the op's own type or name. For example,
    (Store {t} ptr val mem) && is64BitInt(val.Type) can miss a store,
    and (Trunc16to8 x) && isSigned(x.Type) => (MOVBreg x) sign-extends
    int8(uint16(...))'s operand by the wrong rule (go.dev/issue/29943).

  - Elem, Key, NumElem, FieldType, and similar structure queries on an
    argument's type or on the {t} of a Store in the match, which can be
    another type than the rule assumes or not a pointer at all:
    (Move {dst.Type.Elem()} ...) of a memmove call moved a type that
    dst merely claimed to point to (go.dev/issue/55122).

  - Decomposition shortcuts such as (StructMake1 x) && x.Type.IsPtr() => x,
    which must test IsPtrShaped: a struct{ m map[K]V } is stored directly
    in an interface but is not IsPtr, so its StructMake1 survived
    decomposition and crashed the compiler (go.dev/issue/63505).`,
	Run: run,
}

var (
	shiftOp = regexp.MustCompile(`^(Lsh|Rsh)\d+U?x\d+$`)
	truncOp = regexp.MustCompile(`^Trunc\d+to\d+$`)
)

// structureMethods are the methods of *types.Type that describe the
// structure of a particular kind of type, and panic for other kinds.
var structureMethods = map[string]bool{
	"Elem": true, "Key": true, "NumElem": true, "ChanDir": true,
	"Field": true, "FieldType": true, "FieldOff": true, "FieldName": true,
	"Fields": true, "NumFields": true, "Params": true, "Results": true,
	"NumParams": true, "NumResults": true, "Recv": true,
}

// aggregateOps are the decomposition ops of dec.rules whose single-element
// forms are identities for pointer-shaped values.
var aggregateOps = map[string]bool{
	"StructMake1": true, "StructMake": true, "ArrayMake1": true,
	"StructSelect": true, "ArraySelect": true,
}

func run(pass *analysis.Pass) error {
	for r := range pass.Rules() {
		if r.IsBlock() || r.Match.Op == nil {
			continue
		}
		c := newChecker(pass, r)
		c.checkOwnType()
		c.checkStructure()
		c.checkDirectIface()
	}
	return nil
}

type checker struct {
	pass *analysis.Pass
	r    *rules.Rule
	// args are the value variables bound to match nodes other than the root.
	args map[string]bool
	// argAux are the type variables bound as the {aux} of a Store, Move,
	// or Zero below the root: the types of other memory operations.
	argAux map[string]string // name -> op
	done   map[string]bool
}

func newChecker(pass *analysis.Pass, r *rules.Rule) *checker {
	c := &checker{pass: pass, r: r, args: map[string]bool{}, argAux: map[string]string{}, done: map[string]bool{}}
	for _, o := range r.MatchOccurrences() {
		switch {
		case o.Kind == rules.OccValue && o.Value != r.Match:
			c.args[o.Name] = true
		case o.Kind == rules.OccAux && o.Value != nil && o.Value != r.Match && o.Value.Op != nil:
			switch o.Value.OpName {
			case "Store", "Move", "Zero":
				c.argAux[o.Name] = o.Value.OpName
			}
		}
	}
	// A name bound at the root as well (x:(Op ...) ... x) is the root.
	for _, o := range r.MatchOccurrences() {
		if o.Kind == rules.OccValue && o.Value == r.Match {
			delete(c.args, o.Name)
		}
	}
	return c
}

func (c *checker) report(key, format string, args ...any) {
	if c.done[key] {
		return
	}
	c.done[key] = true
	c.pass.Reportf(c.r.Pos, format, args...)
}

// argTypeOf reports whether x is X.Type for an argument variable X,
// and returns X.
func (c *checker) argTypeOf(x ast.Expr) (string, bool) {
	sel, ok := x.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Type" {
		return "", false
	}
	id, ok := sel.X.(*ast.Ident)
	if !ok || !c.args[id.Name] {
		return "", false
	}
	return id.Name, true
}

// checkOwnType reports conditions of width- and sign-defined ops that
// read an argument's type.
func (c *checker) checkOwnType() {
	if c.r.CondExpr == nil || !c.r.Match.Op.IsGeneric() {
		return
	}
	op := c.r.Match.OpName
	var why string
	switch {
	case op == "Store" || op == "Move" || op == "Zero":
		why = fmt.Sprintf("%s's width and register class come from its {t}; "+
			"the argument may be a copy of a value of another type, "+
			"such as a 4-byte value stored by a 2-byte store once (Trunc32to16 x) is lowered to x", op)
	case shiftOp.MatchString(op):
		why = fmt.Sprintf("%s's operand widths and signedness are fixed by its name; "+
			"the argument may be a copy of a value of another type", op)
	case truncOp.MatchString(op):
		why = fmt.Sprintf("the representation of %s's result follows the result type <t>, not the operand's: "+
			"int8(uint16(x)) truncates an unsigned operand to a signed result (go.dev/issue/29943)", op)
	default:
		return
	}
	ast.Inspect(c.r.CondExpr, func(n ast.Node) bool {
		x, ok := n.(ast.Expr)
		if !ok {
			return true
		}
		if name, ok := c.argTypeOf(x); ok {
			c.report("own:"+name, "condition reads %s.Type: %s", name, why)
			return false
		}
		return true
	})
}

// checkStructure reports structure queries on argument types.
func (c *checker) checkStructure() {
	check := func(where, text string) {
		if text == "" {
			return
		}
		x, err := parser.ParseExpr(text)
		if err != nil {
			return
		}
		c.structure(where, x)
	}
	if c.r.CondExpr != nil {
		c.structure("condition", c.r.CondExpr)
	}
	for _, res := range c.r.ResultValues() {
		res.Walk(func(n *rules.Value) bool {
			if n.IsLeaf() {
				return false
			}
			check("result", n.Type)
			check("result", n.AuxInt)
			check("result", n.Aux)
			return true
		})
	}
}

func (c *checker) structure(where string, root ast.Expr) {
	ast.Inspect(root, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || !structureMethods[sel.Sel.Name] {
			return true
		}
		m := sel.Sel.Name
		if name, ok := c.argTypeOf(sel.X); ok {
			c.report("struct:"+name+"."+m, "%s calls %s.Type.%s(), but an argument's type is unreliable: "+
				"conversions between pointer and other same-shaped types are copies, so %s may have another "+
				"%s type than the one the rule needs, or a type without %s (go.dev/issue/55122, go.dev/issue/30061); "+
				"derive it from the root's own type or aux", where, name, m, name, kindOf(m), m)
			return false
		}
		recv := sel.X
		if ta, ok := recv.(*ast.TypeAssertExpr); ok {
			recv = ta.X
		}
		if id, ok := recv.(*ast.Ident); ok {
			if op, ok := c.argAux[id.Name]; ok {
				c.report("struct:"+id.Name+"."+m, "%s calls %s.%s() on the {%s} of a %s in the match, the type of the value "+
					"that %s stored, which can be a type without %s, such as unsafe.Pointer or uintptr "+
					"(go.dev/issue/30061), or another %s type (go.dev/issue/55122)",
					where, id.Name, m, id.Name, op, op, m, kindOf(m))
				return false
			}
		}
		return true
	})
}

func kindOf(method string) string {
	switch method {
	case "Elem":
		return "pointer"
	case "Key":
		return "map"
	case "NumElem":
		return "array"
	case "Params", "Results", "NumParams", "NumResults", "Recv":
		return "func"
	case "ChanDir":
		return "chan"
	}
	return "struct"
}

// checkDirectIface reports decomposition identities guarded by IsPtr.
func (c *checker) checkDirectIface() {
	m := c.r.Match
	if !m.Op.IsGeneric() || !aggregateOps[m.OpName] || c.r.Result == nil || !c.r.Result.IsVar() || c.r.CondExpr == nil {
		return
	}
	ast.Inspect(c.r.CondExpr, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}
		sel, ok := call.Fun.(*ast.SelectorExpr)
		if !ok || sel.Sel.Name != "IsPtr" {
			return true
		}
		recv := exprString(sel.X)
		c.report("iface", "%s is an identity for direct-interface (pointer-shaped) aggregates, but the condition tests "+
			"%s.IsPtr(): a struct{ m map[K]V } is pointer-shaped but not IsPtr, so its %s is never decomposed "+
			"(go.dev/issue/63505); test IsPtrShaped", m.OpName, recv, m.OpName)
		return false
	})
}

// exprString formats a receiver expression.
func exprString(x ast.Expr) string {
	switch x := x.(type) {
	case *ast.Ident:
		return x.Name
	case *ast.SelectorExpr:
		return exprString(x.X) + "." + x.Sel.Name
	}
	return strings.TrimSpace(fmt.Sprint(x))
}
