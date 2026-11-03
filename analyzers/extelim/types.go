package extelim

import (
	"fmt"
	"maps"
	"regexp"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// ssaType abstracts the *types.Type of an integer-like SSA value:
// its size and signedness, and whether it is a bool.
type ssaType uint8

const (
	tBool ssaType = iota
	tInt8
	tUint8
	tInt16
	tUint16
	tInt32
	tUint32
	tInt64
	tUint64
	numTypes
)

var typeNames = [...]string{"bool", "int8", "uint8", "int16", "uint16", "int32", "uint32", "int64", "uint64"}

func (t ssaType) String() string { return typeNames[t] }
func (t ssaType) isInt() bool    { return t != tBool }
func (t ssaType) signed() bool   { return t.isInt() && t%2 == 1 }
func (t ssaType) size() int64 {
	if t == tBool {
		return 1
	}
	return 1 << ((t - 1) / 2)
}

func (t ssaType) method(name string) val {
	switch name {
	case "Size":
		return intVal(kInt64, t.size())
	case "IsSigned":
		return boolVal(t.signed())
	case "IsBoolean":
		return boolVal(t == tBool)
	case "IsInteger":
		return boolVal(t.isInt())
	case "IsFloat", "IsComplex", "IsMemory", "IsFlags", "IsTuple", "IsVoid", "IsSIMD":
		return boolVal(false)
	}
	return unknown
}

// typNames are the types rules name directly.
var typNames = map[string]ssaType{
	"typ.Bool": tBool, "typ.Int8": tInt8, "typ.UInt8": tUint8, "typ.Int16": tInt16, "typ.UInt16": tUint16,
	"typ.Int32": tInt32, "typ.UInt32": tUint32, "typ.Int64": tInt64, "typ.UInt64": tUint64,
	"typ.Int": tInt64, "typ.UInt": tUint64, "typ.Uintptr": tUint64, "typ.BytePtr": tUint64,
}

// opTypNames are the default types in op tables (Op.Typ).
var opTypNames = map[string]ssaType{
	"Bool": tBool, "Int8": tInt8, "UInt8": tUint8, "Int16": tInt16, "UInt16": tUint16,
	"Int32": tInt32, "UInt32": tUint32, "Int64": tInt64, "UInt64": tUint64,
	"Int": tInt64, "UInt": tUint64, "Uintptr": tUint64, "BytePtr": tUint64,
	"bool": tBool, "int8": tInt8, "uint8": tUint8, "int16": tInt16, "uint16": tUint16,
	"int32": tInt32, "uint32": tUint32, "int64": tInt64, "uint64": tUint64,
}

// typeSet is a set of ssaTypes.
type typeSet uint16

const allTypes typeSet = 1<<numTypes - 1

func setOf(ts ...ssaType) typeSet {
	var s typeSet
	for _, t := range ts {
		s |= 1 << t
	}
	return s
}

func (s typeSet) has(t ssaType) bool { return s&(1<<t) != 0 }

func (s typeSet) all() []ssaType {
	var ts []ssaType
	for t := range numTypes {
		if s.has(t) {
			ts = append(ts, t)
		}
	}
	return ts
}

// opTypes computes, for each op of an arch, the types its values may have.
//
// It starts from the generic ops, whose types follow from their signatures
// (SignExt8to32 has a 32-bit type of either signedness: uint32(int8(x)) is
// a SignExt8to32 of type uint32), and propagates them through every rule of
// the arch that creates a value: a value keeps the type of the value it
// replaces unless the rule gives it one, and a type variable stands for
// the types of the value it was bound at, as narrowed by the condition.
// The result over-approximates: if the arch's rules can create an op with
// a type, that type is in the op's set.
type opTypes struct {
	// types maps an op to the types it is created with, keyed by the
	// creating node's auxint if that is an integer literal (so that the
	// types of ANDconst [1] do not leak into a match of ANDconst [0xff]),
	// or by "" otherwise. It describes the values a pass may see: see
	// bySet and forSet.
	types map[*ops.Op]map[string]typeSet
	// bySet holds types for each pass (rule set) of the arch: the values
	// that survive earlier passes and the values the pass creates.
	bySet map[*rules.RuleSet]map[*ops.Op]map[string]typeSet
	// why records, for each op and type, a rule that creates the op
	// with that type.
	why map[*ops.Op]map[ssaType]*rules.Rule
}

// passOrder is the order in which the compiler runs an arch's rule sets.
var passOrder = []string{"", "latelower", "splitload"}

func newOpTypes(c *rules.Corpus, arch string) *opTypes {
	ot := &opTypes{
		bySet: make(map[*rules.RuleSet]map[*ops.Op]map[string]typeSet),
		why:   make(map[*ops.Op]map[ssaType]*rules.Rule),
	}
	survivors := make(map[*ops.Op]map[string]typeSet)
	for _, suffix := range passOrder {
		set := c.Set(arch + suffix)
		if set == nil {
			continue
		}
		ot.types = make(map[*ops.Op]map[string]typeSet)
		for op, m := range survivors {
			ot.types[op] = maps.Clone(m)
		}
		ot.createdBy(set.Rules)
		ot.bySet[set] = ot.types

		// A pass runs until no rule applies, so values that a rule for
		// their op matches whatever their args don't survive it. For
		// example, (MOVBUreg x) && v.Type.Size() <= 1 => x leaves no
		// MOVBUreg of a 1-byte type for later passes.
		survivors = make(map[*ops.Op]map[string]typeSet)
		for op, m := range ot.types {
			gone := consumed(set.ByOp[op])
			survivors[op] = make(map[string]typeSet)
			for k, ts := range m {
				survivors[op][k] = ts &^ gone
			}
		}
	}
	return ot
}

// forSet makes ot describe the values that set's rules see.
func (ot *opTypes) forSet(set *rules.RuleSet) { ot.types = ot.bySet[set] }

// createdBy adds the types of the values that rs create, to a fixed point.
func (ot *opTypes) createdBy(rs []*rules.Rule) {
	for changed := true; changed; {
		changed = false
		for _, r := range rs {
			for _, n := range resultNodes(r) {
				if n.Op == nil || n.Op.IsGeneric() {
					continue
				}
				key := auxKey(n.AuxInt)
				m := ot.types[n.Op]
				if m == nil {
					m = make(map[string]typeSet)
					ot.types[n.Op] = m
				}
				add := ot.resultType(r, n) &^ m[key]
				if add == 0 {
					continue
				}
				changed = true
				m[key] |= add
				if ot.why[n.Op] == nil {
					ot.why[n.Op] = make(map[ssaType]*rules.Rule)
				}
				for _, t := range add.all() {
					if ot.why[n.Op][t] == nil {
						ot.why[n.Op][t] = r
					}
				}
			}
		}
	}
}

// consumed returns the types for which one of rs, the rules for an op,
// rewrites every value of the op.
func consumed(rs []*rules.Rule) typeSet {
	var out typeSet
	for _, r := range rs {
		if !matchesAll(r.Match) {
			continue
		}
		for _, t := range allTypes.all() {
			en := env{"v.Type": {k: kType, t: t}}
			if rules.IsVarText(r.Match.Type) {
				en[r.Match.Type] = val{k: kType, t: t}
			}
			if r.CondExpr == nil {
				out |= setOf(t)
			} else if c := eval(r.CondExpr, en); c.k == kBool && c.b {
				out |= setOf(t)
			}
		}
	}
	return out
}

// auxKey returns the key under which opTypes files a node with auxint x.
func auxKey(x string) string {
	if x == "" || rules.IsVarText(x) {
		return ""
	}
	if v := evalString(x, nil); v.k.isInt() {
		return fmt.Sprint(v.i)
	}
	return ""
}

// of returns the types of values with op.
func (ot *opTypes) of(op *ops.Op) typeSet {
	if op == nil {
		return allTypes
	}
	if op.IsGeneric() {
		return genericTypes(op)
	}
	var ts typeSet
	for _, t := range ot.types[op] {
		ts |= t
	}
	return ts
}

// ofNode returns the types of values that match node n.
func (ot *opTypes) ofNode(n *rules.Value) typeSet {
	if n.Op == nil || n.Op.IsGeneric() {
		return ot.of(n.Op)
	}
	key := auxKey(n.AuxInt)
	if key == "" {
		return ot.of(n.Op)
	}
	// Constants in auxints are sign-extended from the width of the
	// value's type, as for generic ConstN (see check.go), so an
	// ANDconst [0xff] is not an 8-bit value.
	return fitting(evalString(n.AuxInt, nil).i, ot.types[n.Op][""]|ot.types[n.Op][key])
}

func genericTypes(op *ops.Op) typeSet {
	sig, ok := opsig.Lookup(op)
	if !ok {
		return allTypes
	}
	switch res := sig.Result; res.Kind {
	case opsig.Bool:
		return setOf(tBool)
	case opsig.Int:
		switch res.Width {
		case 8:
			return setOf(tInt8, tUint8)
		case 16:
			return setOf(tInt16, tUint16)
		case 32:
			return setOf(tInt32, tUint32)
		case 64:
			return setOf(tInt64, tUint64)
		}
		return allTypes &^ setOf(tBool)
	case opsig.Ptr:
		return setOf(tUint64)
	case opsig.Any, opsig.Unknown, opsig.Tuple, opsig.Results:
		return allTypes
	}
	return 0 // floats, memory, flags, ...: not integer-like
}

// explain returns why op can have type t, or "".
func (ot *opTypes) explain(op *ops.Op, t ssaType) string {
	r := ot.why[op][t]
	if r == nil {
		return ""
	}
	return fmt.Sprintf("%s can have type %s (%s:%d)", op.Name, t, baseName(r.Pos.File), r.Pos.Line)
}

// resultNodes returns the values a rule creates: the compound nodes of its
// result side.
func resultNodes(r *rules.Rule) []*rules.Value {
	var ns []*rules.Value
	for _, v := range r.ResultValues() {
		v.Walk(func(n *rules.Value) bool {
			if n.Op != nil {
				ns = append(ns, n)
			}
			return true
		})
	}
	return ns
}

// resultType returns the types the result node n of r may have.
func (ot *opTypes) resultType(r *rules.Rule, n *rules.Value) typeSet {
	switch {
	case n.Type != "":
		return ot.typeExpr(r, n.Type)
	case !r.IsBlock() && n == r.Result && r.Placement == "":
		return ot.typeExpr(r, "v.Type")
	}
	if t, ok := opTypNames[n.Op.Typ]; ok {
		return setOf(t)
	}
	if n.Op.Typ == "" {
		return allTypes
	}
	return 0
}

// typeExpr returns the types that the Go expression x, in a result's
// <type>, may denote.
func (ot *opTypes) typeExpr(r *rules.Rule, x string) typeSet {
	if t, ok := typNames[x]; ok {
		return setOf(t)
	}
	if strings.HasPrefix(x, "typ.") || strings.HasPrefix(x, "types.") {
		return 0 // typ.Float64, types.TypeFlags, ...
	}
	// Find the match node whose type x names, and the name by which the
	// condition refers to that type.
	var node *rules.Value
	name := x
	switch {
	case x == "v.Type":
		if r.IsBlock() {
			return allTypes
		}
		node = r.Match
		if node.Type != "" && rules.IsVarText(node.Type) {
			name = node.Type // the condition may use t for v.Type
		}
	case strings.HasSuffix(x, ".Type") && rules.IsVarText(strings.TrimSuffix(x, ".Type")):
		for _, o := range r.MatchVars()[strings.TrimSuffix(x, ".Type")] {
			if o.Kind == rules.OccValue {
				node = o.Value
				break
			}
		}
	case rules.IsVarText(x):
		for _, o := range r.MatchVars()[x] {
			if o.Kind == rules.OccType {
				node = o.Value
				break
			}
		}
	}
	if node == nil {
		return allTypes
	}
	ts := ot.ofNode(node)
	if node == r.Match && !r.IsBlock() {
		return ot.narrow(r, fitConstArgs(node, ts&^ot.shadowed(r)), name, "v.Type")
	}
	return ot.narrow(r, ts, name)
}

// narrow removes from ts the types for which r's condition is false when
// the given names denote the type.
func (ot *opTypes) narrow(r *rules.Rule, ts typeSet, names ...string) typeSet {
	if r.CondExpr == nil {
		return ts
	}
	var out typeSet
	for _, t := range ts.all() {
		en := env{}
		for _, n := range names {
			en[n] = val{k: kType, t: t}
		}
		if c := eval(r.CondExpr, en); c.k != kBool || c.b {
			out |= setOf(t)
		}
	}
	return out
}

// fitConstArgs removes from ts, the types of n, those too narrow for a
// constant arg of n: (AND (MOVDconst [0xffffffff]) x) is not a 32-bit AND,
// since a 32-bit constant would be sign-extended (-1).
func fitConstArgs(n *rules.Value, ts typeSet) typeSet {
	for _, a := range n.Args {
		if a.Op == nil || !constOpRE.MatchString(a.Op.Name) || auxKey(a.AuxInt) == "" {
			continue
		}
		ts &= fitting(evalString(a.AuxInt, nil).i, ts)
	}
	return ts
}

var constOpRE = regexp.MustCompile(`^MOV[A-Z]?const$`)

// fitting returns the types of ts whose width can hold the constant l,
// sign-extended as in a generic ConstN.
func fitting(l int64, ts typeSet) typeSet {
	for _, t := range ts.all() {
		if w := 8 * t.size(); w < 64 && l<<(64-w)>>(64-w) != l {
			ts &^= setOf(t)
		}
	}
	return ts
}

// shadowed returns the types of r's matched value for which an earlier
// rule for the same op always matches instead: one that matches any value
// of the op (its args are distinct variables, its auxints unconstrained)
// whose condition is true for the type. For example, after
//
//	(Trunc64to8 <t> x) && t.IsSigned() => (MOVBreg x)
//
// the rule (Trunc64to8 x) => (MOVBZreg x) sees only unsigned types.
func (ot *opTypes) shadowed(r *rules.Rule) typeSet {
	rs := r.Set.ByOp[r.Match.Op]
	for i, e := range rs {
		if e == r {
			return consumed(rs[:i])
		}
	}
	return 0
}

// matchesAll reports whether m matches every value of its op.
func matchesAll(m *rules.Value) bool {
	if m.Ellipsis {
		return true
	}
	for _, x := range []string{m.Type, m.AuxInt, m.Aux} {
		if x != "" && !rules.IsVarText(x) && x != "_" {
			return false
		}
	}
	seen := map[string]bool{}
	for _, a := range m.Args {
		if !a.IsLeaf() {
			return false
		}
		if a.Name != "_" {
			if seen[a.Name] {
				return false
			}
			seen[a.Name] = true
		}
	}
	return true
}

func baseName(p string) string {
	if i := strings.LastIndexAny(p, `/\`); i >= 0 {
		return p[i+1:]
	}
	return p
}
