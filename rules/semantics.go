package rules

import (
	"go/token"
)

// This file holds helpers that encode rulegen's semantics, so that
// analyzers don't each reimplement them subtly wrong.

// OccurrenceKind says what part of a match an Occurrence names.
type OccurrenceKind uint8

const (
	OccValue  OccurrenceKind = iota // a value: leaf variable x, or binding name x in x:(...)
	OccType                         // <t>
	OccAuxInt                       // [c]
	OccAux                          // {s}
)

// An Occurrence is a variable in a match.
type Occurrence struct {
	Name string
	Kind OccurrenceKind
	// Value is the node that is bound (OccValue) or whose type, auxint,
	// or aux is bound. It is nil for a block's auxint or aux.
	Value *Value
}

// IsVarText reports whether s, the text of a leaf or of a <type>, [auxint],
// or {aux} in a match, is a variable rather than a Go expression to compare
// against. For example, x and c are variables; 0, nil, and typ.UInt64 are not.
// The wildcard _ is not a variable.
func IsVarText(s string) bool {
	return token.IsIdentifier(s) && s != "_" && !predeclared[s]
}

// MatchOccurrences returns the variables in r's match, in source order.
//
// rulegen binds a variable at its first occurrence and turns each later
// occurrence of the same name into an equality check: pointer equality for
// values (so (Sub64 x x) matches only when both args are the same *Value),
// and == for types, auxints, and auxes. A name is never bound to two
// different kinds of things in a valid rule.
//
// A <type>, [auxint], or {aux} that is not a variable (see IsVarText) is
// instead compared against the Go expression it contains: [0] matches only
// auxint 0, and <typ.UInt64> matches only that type.
//
// MatchOccurrences omits _ and non-variable texts.
func (r *Rule) MatchOccurrences() []Occurrence {
	var occs []Occurrence
	add := func(name string, kind OccurrenceKind, v *Value) {
		if IsVarText(name) {
			occs = append(occs, Occurrence{name, kind, v})
		}
	}
	var walk func(v *Value)
	walk = func(v *Value) {
		add(v.Name, OccValue, v)
		add(v.Type, OccType, v)
		add(v.AuxInt, OccAuxInt, v)
		add(v.Aux, OccAux, v)
		for _, a := range v.Args {
			walk(a)
		}
	}
	if r.IsBlock() {
		add(r.MatchBlock.AuxInt, OccAuxInt, nil)
		add(r.MatchBlock.Aux, OccAux, nil)
		for _, c := range r.MatchBlock.Controls {
			walk(c)
		}
	} else {
		walk(r.Match)
	}
	return occs
}

// MatchVars returns r's MatchOccurrences grouped by name.
// A name with more than one occurrence is an equality constraint.
func (r *Rule) MatchVars() map[string][]Occurrence {
	m := make(map[string][]Occurrence)
	for _, o := range r.MatchOccurrences() {
		m[o.Name] = append(m[o.Name], o)
	}
	return m
}

// Commutes reports whether matching v tries both orders of its first two
// args, that is, whether v's op is commutative.
//
// The generated matcher tries the written order first, then the swapped
// order, checking the condition for each; the first that succeeds binds the
// variables used by the result. (rulegen elides the swapped attempt when it
// provably can't matter, such as for (Add64 x x); that is not observable.)
func (v *Value) Commutes() bool {
	return v.Op != nil && v.Op.Commutative && len(v.Args) >= 2
}

// Commutations returns the match s-expressions equivalent to v under
// commutativity, in the order the generated matcher tries them: every
// combination of swapping the first two args of each commutative op.
// The first element is v itself. Nodes are shared, not copied, where possible.
func Commutations(v *Value) []*Value {
	if v.IsLeaf() || len(v.Args) == 0 {
		return []*Value{v}
	}
	orders := [][]*Value{v.Args}
	if v.Commutes() {
		swapped := append([]*Value{v.Args[1], v.Args[0]}, v.Args[2:]...)
		orders = append(orders, swapped)
	}
	var res []*Value
	for _, args := range orders {
		// Each arg's variants, nested with earlier args outermost.
		combos := [][]*Value{nil}
		for _, a := range args {
			var next [][]*Value
			for _, prefix := range combos {
				for _, av := range Commutations(a) {
					next = append(next, append(prefix[:len(prefix):len(prefix)], av))
				}
			}
			combos = next
		}
		for _, c := range combos {
			nv := *v
			nv.Args = c
			res = append(res, &nv)
		}
	}
	return res
}

// TypeSource says where a result value's type comes from.
type TypeSource uint8

const (
	// TypeExplicit: the rule gives the type, as in (Foo <t> x).
	TypeExplicit TypeSource = iota
	// TypeOpDefault: the op's default type (ops.Op.Typ).
	TypeOpDefault
	// TypeInherited: the top-level result of a value rule without @block
	// placement and without an explicit type keeps the type of the value
	// being rewritten (v.Type), not the op's default type.
	TypeInherited
	// TypeExisting: the result is a leaf, an existing value with its own
	// type. (At top level, v becomes a Copy of it and keeps v's own type.)
	TypeExisting
)

// ResultType reports the type rulegen gives result value v of r, which
// must be r.Result, a result block control, or a descendant of one.
// For TypeExplicit, typ is the Go expression in the rule; for
// TypeOpDefault, it is the op's type name (see ops.TypeExpr);
// otherwise it is "".
func (r *Rule) ResultType(v *Value) (typ string, src TypeSource) {
	switch {
	case v.IsLeaf():
		return "", TypeExisting
	case v.Type != "":
		return v.Type, TypeExplicit
	case v == r.Result && r.Placement == "":
		return "", TypeInherited
	}
	return v.Op.Typ, TypeOpDefault
}

// Unconditional reports whether r applies to every value of its match op
// (or every block of its match kind): it has no condition, and its match
// constrains nothing but the top-level op. For example,
// (Neg64 x) => (Sub64 (Const64 [0]) x) is unconditional, but (Neg64 (Neg64 x))
// and (Add64 x x) are not. A variadic op's argument count is a constraint
// unless written (Op ___).
//
// rulegen rejects a value rule that follows an unconditional rule for
// the same op.
func (r *Rule) Unconditional() bool {
	if r.Cond != "" {
		return false
	}
	seen := map[string]bool{}
	fresh := func(s string) bool {
		if s == "" || s == "_" {
			return true
		}
		if !IsVarText(s) || seen[s] {
			return false
		}
		seen[s] = true
		return true
	}
	if r.IsBlock() {
		b := r.MatchBlock
		if !fresh(b.AuxInt) || !fresh(b.Aux) {
			return false
		}
		for _, c := range b.Controls {
			if !c.IsLeaf() || !fresh(c.Name) {
				return false
			}
		}
		return true
	}
	m := r.Match
	if m.Ellipsis {
		return true
	}
	if !fresh(m.Type) || !fresh(m.AuxInt) || !fresh(m.Aux) {
		return false
	}
	if m.Op.ArgLength == -1 && !(m.Rest && len(m.Args) == 0) {
		return false
	}
	for _, a := range m.Args {
		if !a.IsLeaf() || !fresh(a.Name) {
			return false
		}
	}
	return true
}
