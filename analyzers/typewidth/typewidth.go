// Package typewidth reports generic ops whose width disagrees with the type
// a rule gives them or with the width of the value they replace or consume.
package typewidth

import (
	"fmt"
	"sort"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "typewidth",
	Doc: `report generic ops whose width disagrees with their type or context

The name of a generic op fixes the width of its result and arguments
(Const64 is 64 bits; Add32 takes and returns 32-bit integers; Lsh32x64
takes a 64-bit count), but nothing ties that width to the type a rule
gives the value. A mismatch is ill-typed SSA, which later passes
mishandle: a value is spilled at its type's size, decomposed by its
type's size, and so on. The analyzer reports:

  - A result op with an explicit type of a different size or kind,
    such as (Const64 <t> [c+d]) where t is the 4-byte type of a
    matched Lsh32x64, or (Mul64 <typ.UInt32> ...), whose product loses
    its upper half when spilled.
  - A result root that inherits the matched value's type but is
    narrower, or a different kind, or (for constants and floats) a
    different width: (Div64F x (Const64F [-1])) => (Neg32F x) negates
    a float64 as a float32. (A wider integer op computing a narrower
    value, as in (Div16 x y) => (Div32 (SignExt16to32 x) ...), is a
    deliberate idiom and is not reported.)
  - In rules that produce generic ops (generic.rules, dec64.rules, ...),
    an argument whose width differs from what its op takes, as in a
    Const32 shift count for Rsh32Ux64.
  - A match that requires an argument of the wrong width, which can
    never match: (IsInBounds (Rsh8Ux64 ...) (Const64 [d])) compares an
    8-bit index with a 64-bit length, but IsInBounds' arguments always
    have the same type.`,
	Run: run,
}

// A shape is the kind and width of a value, as far as known.
type shape struct {
	kind  opsig.Kind // Int, Float, or Bool; Unknown if not known
	width int        // in bits; 0 if not known
}

func (s shape) known() bool { return s.kind != opsig.Unknown && (s.kind == opsig.Bool || s.width > 0) }

// String describes s with an indefinite article: "a 32-bit integer".
func (s shape) String() string {
	a := "a"
	if s.width == 8 {
		a = "an"
	}
	switch s.kind {
	case opsig.Int:
		return fmt.Sprintf("%s %d-bit integer", a, s.width)
	case opsig.Float:
		return fmt.Sprintf("%s %d-bit float", a, s.width)
	case opsig.Bool:
		return "a bool"
	}
	return "an unknown"
}

// opShape returns the shape of the result of generic op node v,
// as fixed by its op.
func opShape(v *rules.Value) shape {
	if v.IsLeaf() || !v.Op.IsGeneric() {
		return shape{}
	}
	sig, ok := opsig.Lookup(v.Op)
	if !ok {
		return shape{}
	}
	return operandShape(sig.Result)
}

func operandShape(o opsig.Operand) shape {
	switch o.Kind {
	case opsig.Int, opsig.Float:
		if o.Width > 0 {
			return shape{o.Kind, o.Width}
		}
	case opsig.Bool:
		return shape{kind: opsig.Bool}
	}
	return shape{}
}

type checker struct {
	pass    *analysis.Pass
	rule    *rules.Rule
	vars    map[string][]rules.Occurrence
	slot    map[*rules.Value]shape // match node -> shape of the arg slot it fills
	reports []string
}

func run(pass *analysis.Pass) error {
	for r := range pass.Rules() {
		if r.IsBlock() {
			continue
		}
		c := &checker{pass: pass, rule: r, vars: r.MatchVars(), slot: map[*rules.Value]shape{}}
		c.check()
		sort.Strings(c.reports)
		for i, msg := range c.reports {
			if i == 0 || msg != c.reports[i-1] {
				pass.Report(r.Pos, msg)
			}
		}
	}
	return nil
}

func (c *checker) reportf(format string, args ...any) {
	c.reports = append(c.reports, fmt.Sprintf(format, args...))
}

func (c *checker) check() {
	r := c.rule
	c.checkMatch(r.Match)
	if r.Result == nil {
		return
	}
	generic := r.Set.Arch.Generic
	var walk func(v *rules.Value, slot shape)
	walk = func(v *rules.Value, slot shape) {
		if v.IsLeaf() {
			return
		}
		var sig opsig.Sig
		if v.Op.IsGeneric() {
			sig, _ = opsig.Lookup(v.Op)
			op := opShape(v)
			typ, src := r.ResultType(v)
			if src == rules.TypeExplicit && op.known() {
				if got, ok := c.typeShape(typ); ok && got.known() {
					c.checkType(v, typ, op, got, slot, generic)
				}
			}
			if src == rules.TypeInherited {
				c.checkRoot(v, op, generic)
			}
			if generic {
				c.checkArgs(v, sig)
			}
		}
		for i, a := range v.Args {
			var as shape
			if sig.Variadic == nil && i < len(sig.Args) {
				as = operandShape(sig.Args[i])
			}
			walk(a, as)
		}
	}
	walk(r.Result, shape{})
}

// checkType checks the explicit type typ, of shape got, of result node v,
// whose op produces a value of shape op and which fills an argument slot
// of shape slot (if known).
func (c *checker) checkType(v *rules.Value, typ string, op, got, slot shape, generic bool) {
	bad := false
	switch {
	case got.kind != op.kind:
		bad = true
	case op.kind == opsig.Bool, got.width == op.width:
	case op.kind == opsig.Float, got.width > op.width:
		// A float has one representation per width; an integer type
		// wider than its op claims bits the op does not define.
		bad = true
	case generic && isConst(v):
		// A narrower type on a wider integer op is how rules compute
		// a narrow value with a wide op, but passes that see a
		// constant (decompose, prove, CSE of rotate counts, ...)
		// trust its type's size.
		bad = true
	case slot.known() && slot.width > got.width:
		// The consumer reads more bits than the type keeps (a spill
		// stores only the type's size).
		c.reportf("(%s <%s> ...) gives %s result the type %s, %s, but its consumer reads %s: the upper bits are lost if it is spilled",
			v.Op.Name, typ, op, typ, got, slot)
		return
	}
	if bad {
		c.reportf("(%s <%s> ...) gives %s result the type %s, %s", v.Op.Name, typ, op, typ, got)
	}
}

func sameShape(a, b shape) bool {
	if a.kind != b.kind {
		return false
	}
	return a.kind == opsig.Bool || a.width == b.width
}

// checkRoot checks result root v, which inherits the type of the matched
// value, against the matched root.
func (c *checker) checkRoot(v *rules.Value, got shape, generic bool) {
	m := c.rule.Match
	want := opShape(m)
	if !got.known() || !want.known() || m.Ellipsis {
		return
	}
	bad := got.kind != want.kind
	if !bad && got.kind != opsig.Bool && got.width != want.width {
		// A wider integer op may compute a narrower value
		// (Div16 => Div32 of extended arguments), but a constant's
		// width must match its type, and a narrower op loses bits.
		bad = got.kind == opsig.Float || got.width < want.width || generic && isConst(v)
	}
	if bad {
		c.reportf("%s produces %s, but the %s it replaces is %s and its type is kept",
			v.Op.Name, got, m.Op.Name, want)
	}
}

func isConst(v *rules.Value) bool {
	return !v.IsLeaf() && v.Op.IsGeneric() && strings.HasPrefix(v.Op.Name, "Const")
}

// checkArgs checks that the arguments of result node v have the widths
// that v's op takes.
func (c *checker) checkArgs(v *rules.Value, sig opsig.Sig) {
	if sig.Variadic != nil {
		return
	}
	for i, a := range v.Args {
		if i >= len(sig.Args) {
			break
		}
		want := operandShape(sig.Args[i])
		if !want.known() || want.kind == opsig.Bool {
			continue
		}
		if !a.IsLeaf() && a.Op.IsGeneric() {
			if typ, src := c.rule.ResultType(a); src == rules.TypeExplicit {
				if ts, ok := c.typeShape(typ); ok && ts.known() && opShape(a).known() && !sameShape(ts, opShape(a)) {
					continue // checkType judges the conflict
				}
			}
		}
		got, desc := c.resultShape(a)
		if got.known() && !sameShape(got, want) {
			c.reportf("%s's argument %d must be %s, but %s is %s", v.Op.Name, i, want, desc, got)
		}
	}
}

// resultShape returns the shape of result node a and a description of it.
func (c *checker) resultShape(a *rules.Value) (shape, string) {
	if !a.IsLeaf() {
		// The type, not the op, is what the SSA checker compares
		// (ssacompile/check.go), and a wide op may compute a narrow
		// value.
		if typ, src := c.rule.ResultType(a); src == rules.TypeExplicit {
			if s, ok := c.typeShape(typ); ok {
				return s, fmt.Sprintf("(%s <%s> ...)", a.Op.Name, typ)
			}
		}
		if !a.Op.IsGeneric() {
			return shape{}, ""
		}
		return opShape(a), a.Op.Name
	}
	if !a.IsVar() {
		return shape{}, ""
	}
	return c.valueShape(a.Name), a.Name
}

// valueShape returns the shape of match value variable name.
func (c *checker) valueShape(name string) shape {
	var s shape
	for _, o := range c.vars[name] {
		if o.Kind != rules.OccValue {
			continue
		}
		t := opShape(o.Value)
		if !t.known() {
			t = c.slot[o.Value]
		}
		if !t.known() {
			continue
		}
		if s.known() && !sameShape(s, t) {
			return shape{} // inconsistent; another check reports the match
		}
		s = t
	}
	return s
}

// checkMatch records the shape of each match node's argument slot and
// reports match nodes that can never fill their slot.
func (c *checker) checkMatch(m *rules.Value) {
	m.Walk(func(v *rules.Value) bool {
		if v.IsLeaf() || !v.Op.IsGeneric() {
			return true
		}
		sig, ok := opsig.Lookup(v.Op)
		if !ok || sig.Variadic != nil {
			return true
		}
		for i, a := range v.Args {
			if i >= len(sig.Args) {
				break
			}
			want := operandShape(sig.Args[i])
			c.slot[a] = want
			// A wider op may compute a narrower value (see checkType), so
			// only a narrower op or a different kind cannot fill the slot.
			got := opShape(a)
			if want.known() && got.known() && (got.kind != want.kind || got.width < want.width) {
				c.reportf("%s's argument %d is always %s, so it is never %s (%s): the rule cannot match",
					v.Op.Name, i, want, a.Op.Name, got)
			}
		}
		if sameTypeArgs[v.Op.Name] && len(v.Args) == 2 {
			a, b := opShape(v.Args[0]), opShape(v.Args[1])
			if a.known() && b.known() && !sameShape(a, b) {
				c.reportf("%s's arguments always have the same type, so they are never %s (%s) and %s (%s): the rule cannot match",
					v.Op.Name, v.Args[0].Op.Name, a, v.Args[1].Op.Name, b)
			}
		}
		return true
	})
}

// sameTypeArgs are generic ops whose two arguments always have the same
// type, although the op does not fix its width (ssagen's extendIndex
// gives bounds-check indexes and lengths type int).
var sameTypeArgs = map[string]bool{
	"IsInBounds":      true,
	"IsSliceInBounds": true,
}

// typeShape returns the shape of the type expression typ in a result.
func (c *checker) typeShape(typ string) (shape, bool) {
	typ = strings.TrimSpace(typ)
	if rest, ok := strings.CutPrefix(typ, "typ."); ok {
		s, ok := typFields[rest]
		return s, ok
	}
	if rest, ok := strings.CutPrefix(typ, "types.Types[types."); ok {
		s, ok := kindTypes[strings.TrimSuffix(rest, "]")]
		return s, ok
	}
	if v, ok := strings.CutSuffix(typ, ".Type"); ok && rules.IsVarText(v) {
		if v == "v" {
			return opShape(c.rule.Match), true
		}
		return c.valueShape(v), true
	}
	if rules.IsVarText(typ) {
		// A type variable: the type of the match node it is bound on.
		for _, o := range c.vars[typ] {
			if o.Kind == rules.OccType && o.Value != nil {
				if s := opShape(o.Value); s.known() {
					return s, true
				}
			}
		}
	}
	return shape{}, false
}

// typFields are the fixed-size fields of ssa.Types (ssa/config.go),
// which rules refer to as typ.X.
var typFields = map[string]shape{
	"Bool":    {kind: opsig.Bool},
	"Int8":    {opsig.Int, 8},
	"Int16":   {opsig.Int, 16},
	"Int32":   {opsig.Int, 32},
	"Int64":   {opsig.Int, 64},
	"UInt8":   {opsig.Int, 8},
	"UInt16":  {opsig.Int, 16},
	"UInt32":  {opsig.Int, 32},
	"UInt64":  {opsig.Int, 64},
	"Float32": {opsig.Float, 32},
	"Float64": {opsig.Float, 64},
}

// kindTypes are the fixed-size types.Types[types.TXXX].
var kindTypes = map[string]shape{
	"TBOOL":    {kind: opsig.Bool},
	"TINT8":    {opsig.Int, 8},
	"TINT16":   {opsig.Int, 16},
	"TINT32":   {opsig.Int, 32},
	"TINT64":   {opsig.Int, 64},
	"TUINT8":   {opsig.Int, 8},
	"TUINT16":  {opsig.Int, 16},
	"TUINT32":  {opsig.Int, 32},
	"TUINT64":  {opsig.Int, 64},
	"TFLOAT32": {opsig.Float, 32},
	"TFLOAT64": {opsig.Float, 64},
}
