package valuekind

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// kind is what sort of thing an SSA value is: a register value, a memory
// state, flags, a tuple, and so on.
type kind uint8

const (
	unknown kind = iota
	value        // a scalar or aggregate value
	mem
	flags
	tuple
	results // a call's results
	void
)

func (k kind) String() string {
	return [...]string{"unknown", "a value", "memory", "flags", "a tuple", "call results", "void"}[k]
}

// class is the register class a scalar value's type calls for.
type class uint8

const (
	anyClass class = iota // unknown, or not a scalar register value
	gp                    // integer, bool, or pointer
	fp                    // float
)

func (c class) String() string {
	return [...]string{"any", "integer", "floating-point"}[c]
}

// shape is the kind of a value and, for a scalar value, its register class.
type shape struct {
	kind  kind
	class class
	elems []shape // for a tuple, when known
}

func (s shape) known() bool { return s.kind != unknown }

// describe formats s for diagnostics.
func (s shape) describe() string {
	if s.kind == value && s.class != anyClass {
		return "an " + s.class.String() + " value"
	}
	if s.kind == value && s.class == anyClass {
		return "a value"
	}
	return s.kind.String()
}

// typeName returns the shape of a type named as in an op's typ field
// ("UInt8", "Flags", "(UInt64,Mem)") or after "typ." in a rule.
func typeName(name string) shape {
	name = strings.TrimSpace(name)
	if strings.HasPrefix(name, "(") && strings.HasSuffix(name, ")") {
		s := shape{kind: tuple}
		for _, e := range strings.Split(name[1:len(name)-1], ",") {
			s.elems = append(s.elems, typeName(e))
		}
		return s
	}
	switch strings.ToLower(name) {
	case "mem":
		return shape{kind: mem}
	case "flags":
		return shape{kind: flags}
	case "void":
		return shape{kind: void}
	case "float32", "float64":
		return shape{kind: value, class: fp}
	case "int8", "int16", "int32", "int64", "int",
		"uint8", "uint16", "uint32", "uint64", "uint", "uintptr",
		"bool", "byteptr":
		return shape{kind: value, class: gp}
	case "int128", "mask", "v128":
		return shape{kind: value}
	}
	if strings.HasPrefix(name, "Vec") {
		return shape{kind: value}
	}
	return shape{}
}

// types.Types[types.TXXX] kinds.
var basicKinds = map[string]shape{
	"TINT8": {kind: value, class: gp}, "TUINT8": {kind: value, class: gp},
	"TINT16": {kind: value, class: gp}, "TUINT16": {kind: value, class: gp},
	"TINT32": {kind: value, class: gp}, "TUINT32": {kind: value, class: gp},
	"TINT64": {kind: value, class: gp}, "TUINT64": {kind: value, class: gp},
	"TINT": {kind: value, class: gp}, "TUINT": {kind: value, class: gp},
	"TUINTPTR": {kind: value, class: gp}, "TBOOL": {kind: value, class: gp},
	"TUNSAFEPTR": {kind: value, class: gp},
	"TFLOAT32":   {kind: value, class: fp}, "TFLOAT64": {kind: value, class: fp},
}

// sigShape converts an opsig operand to a shape.
func sigShape(o opsig.Operand) shape {
	switch o.Kind {
	case opsig.Int, opsig.Bool, opsig.Ptr:
		return shape{kind: value, class: gp}
	case opsig.Float:
		return shape{kind: value, class: fp}
	case opsig.String, opsig.Slice, opsig.Interface, opsig.Complex,
		opsig.Struct, opsig.Array, opsig.Vector:
		return shape{kind: value}
	case opsig.Mem:
		return shape{kind: mem}
	case opsig.Flags:
		return shape{kind: flags}
	case opsig.Void:
		return shape{kind: void}
	case opsig.Results:
		return shape{kind: results}
	case opsig.Tuple:
		s := shape{kind: tuple}
		for _, e := range o.Elems {
			s.elems = append(s.elems, sigShape(e))
		}
		return s
	}
	return shape{}
}

// polymorphic ops take their type, and so their shape, from the rule.
var polymorphic = map[string]bool{
	"Copy": true, "Phi": true, "Select0": true, "Select1": true, "SelectN": true,
	"Last": true, "CondSelect": true, "Load": true, "Arg": true, "ArgIntReg": true,
	"ArgFloatReg": true, "FwdRef": true, "Unknown": true, "InlMark": true,
}

// facts holds what valuekind knows about ops in a corpus.
type facts struct {
	// selected reports ops that appear as the argument of Select0 or
	// Select1 in some rule. Such an op produces a tuple whatever its
	// default type says (PPC64's LoweredAtomicLoad8 has typ UInt8 but
	// is a (value, memory) tuple), so its default type is not evidence.
	selected map[*ops.Op]bool
	// inferred gives the shape of ops whose tables don't say (AMD64's
	// FlagEQ has no typ and no outputs), from the rules that produce them.
	inferred map[*ops.Op]shape
}

func newFacts(c *rules.Corpus) *facts {
	f := &facts{selected: map[*ops.Op]bool{}, inferred: map[*ops.Op]shape{}}
	for _, s := range c.Sets {
		for _, r := range s.Rules {
			visit := func(v *rules.Value) bool {
				if v.Op != nil && (v.OpName == "Select0" || v.OpName == "Select1") && len(v.Args) == 1 && v.Args[0].Op != nil {
					f.selected[v.Args[0].Op] = true
				}
				return true
			}
			for _, v := range r.MatchValues() {
				v.Walk(visit)
			}
			for _, v := range r.ResultValues() {
				v.Walk(visit)
			}
		}
	}
	// Infer the shapes of ops the tables leave unknown from the rules
	// that produce them at top level, inheriting the matched value's type.
	conflict := map[*ops.Op]bool{}
	for _, s := range c.Sets {
		for _, r := range s.Rules {
			if r.IsBlock() || r.Result == nil || r.Result.IsLeaf() || r.Result.Type != "" || r.Placement != "" {
				continue
			}
			op := r.Result.Op
			if f.intrinsic(op).known() || polymorphic[op.Name] {
				continue
			}
			m := f.intrinsic(r.Match.Op)
			if !m.known() {
				continue
			}
			if old, ok := f.inferred[op]; ok && old.kind != m.kind {
				conflict[op] = true
			}
			f.inferred[op] = shape{kind: m.kind}
		}
	}
	for op := range conflict {
		delete(f.inferred, op)
	}
	return f
}

// intrinsic returns the shape an op's values have regardless of the type
// a rule gives them: from the op's default type, or for an arch op
// without one, from its register outputs. It returns an unknown shape for
// polymorphic ops and ops whose tables don't determine a shape.
func (f *facts) intrinsic(op *ops.Op) shape {
	if op == nil || polymorphic[op.Name] || op.SIMD {
		return shape{}
	}
	if op.Typ != "" {
		s := typeName(op.Typ)
		if s.kind == value && (f.selected[op] || !op.IsGeneric() && hasNonRegArg(op)) {
			// The default type of an op with a memory argument may
			// leave out the memory: PPC64's LoweredAtomicLoad64 has
			// typ Int64, but every value of it is an (Int64, Mem)
			// tuple, whose type comes from the AtomicLoad64 it lowers.
			return shape{}
		}
		return s
	}
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		if !ok || sig.SIMD {
			return shape{}
		}
		return sigShape(sig.Result)
	}
	writes := strings.Contains(op.SymEffect, "Write") || strings.Contains(op.SymEffect, "Wr")
	switch len(op.Reg.Outputs) {
	case 0:
		if writes && !op.Call {
			return shape{kind: mem}
		}
	case 1:
		if writes || f.selected[op] || hasNonRegArg(op) {
			// A memory or flags argument: possibly a (value, memory)
			// tuple, such as an atomic load, which the tables don't
			// distinguish from a plain load.
			return shape{}
		}
		if c := outClass(op); c != anyClass {
			return shape{kind: value, class: c}
		}
	case 2:
		return shape{kind: tuple}
	}
	return shape{}
}

// hasNonRegArg reports whether op has an argument (memory or flags) not
// passed in a general register class.
func hasNonRegArg(op *ops.Op) bool {
	if op.ArgLength < 0 {
		return true
	}
	n := 0
	for _, m := range op.Reg.Inputs {
		if !m.Empty() {
			n++
		}
	}
	return int(op.ArgLength) > n
}

// outClass returns the register class of op's single output.
func outClass(op *ops.Op) class {
	if op.IsGeneric() || len(op.Reg.Outputs) != 1 {
		return anyClass
	}
	return regClass(op.Arch, op.Reg.Outputs[0])
}

func regClass(a *ops.Arch, m ops.RegMask) class {
	c := a.Classify(m)
	switch {
	case c&ops.RegGP != 0 && c&(ops.RegFP|ops.RegSIMD|ops.RegSIMDMask) == 0:
		return gp
	case c&ops.RegFP != 0 && c&(ops.RegGP|ops.RegSIMDMask) == 0:
		return fp
	}
	return anyClass
}

// env resolves the shapes of type expressions in one rule.
type env struct {
	f    *facts
	r    *rules.Rule
	vars map[string][]rules.Occurrence
	// parent maps each match node to its parent and arg index.
	parent map[*rules.Value]*rules.Value
}

func newEnv(f *facts, r *rules.Rule) *env {
	e := &env{f: f, r: r, vars: r.MatchVars(), parent: map[*rules.Value]*rules.Value{}}
	for _, m := range r.MatchValues() {
		m.Walk(func(v *rules.Value) bool {
			for _, a := range v.Args {
				e.parent[a] = v
			}
			return true
		})
	}
	return e
}

// matchShape returns the shape of match node n's type.
func (e *env) matchShape(n *rules.Value) shape {
	if n.IsLeaf() {
		p := e.parent[n]
		if p == nil || p.Op == nil || !p.Op.IsGeneric() {
			return shape{}
		}
		sig, ok := opsig.Lookup(p.Op)
		if !ok || sig.SIMD {
			return shape{}
		}
		for i, a := range p.Args {
			if a == n {
				if sig.Variadic != nil {
					return sigShape(*sig.Variadic)
				}
				return sigShape(sig.Args[i])
			}
		}
		return shape{}
	}
	if n.Type != "" && !rules.IsVarText(n.Type) {
		return e.exprShape(n.Type)
	}
	if s := e.f.intrinsic(n.Op); s.known() {
		return s
	}
	return e.f.inferred[n.Op]
}

// valueVar returns the match node bound to the value variable name.
func (e *env) valueVar(name string) *rules.Value {
	for _, o := range e.vars[name] {
		if o.Kind == rules.OccValue {
			return o.Value
		}
	}
	return nil
}

// exprShape returns the shape of the type denoted by Go expression text,
// as used in a <type>.
func (e *env) exprShape(text string) shape {
	x, err := parser.ParseExpr(text)
	if err != nil {
		return shape{}
	}
	switch x := x.(type) {
	case *ast.Ident:
		if x.Name == "v" {
			return e.matchShape(e.r.Match)
		}
		for _, o := range e.vars[x.Name] {
			if o.Kind == rules.OccType && o.Value != nil {
				return e.matchShape(o.Value)
			}
		}
	case *ast.SelectorExpr:
		pkg, ok := x.X.(*ast.Ident)
		if !ok {
			break
		}
		switch {
		case pkg.Name == "typ":
			return typeName(x.Sel.Name)
		case pkg.Name == "types" && strings.HasPrefix(x.Sel.Name, "Type"):
			return typeName(strings.TrimPrefix(x.Sel.Name, "Type"))
		case x.Sel.Name == "Type":
			if pkg.Name == "v" && e.r.Match != nil {
				return e.matchShape(e.r.Match)
			}
			if n := e.valueVar(pkg.Name); n != nil {
				return e.matchShape(n)
			}
		}
	case *ast.CallExpr:
		if sel, ok := x.Fun.(*ast.SelectorExpr); ok && isPkg(sel.X, "types") && sel.Sel.Name == "NewTuple" {
			s := shape{kind: tuple}
			for _, a := range x.Args {
				s.elems = append(s.elems, e.exprShape(exprText(text, a)))
			}
			return s
		}
	case *ast.IndexExpr:
		if sel, ok := x.X.(*ast.SelectorExpr); ok && isPkg(sel.X, "types") && sel.Sel.Name == "Types" {
			if idx, ok := x.Index.(*ast.SelectorExpr); ok && isPkg(idx.X, "types") {
				return basicKinds[idx.Sel.Name]
			}
		}
	}
	return shape{}
}

func isPkg(x ast.Expr, name string) bool {
	id, ok := x.(*ast.Ident)
	return ok && id.Name == name
}

// exprText returns the source of sub-expression x of src, which was
// parsed by parser.ParseExpr (positions are offsets plus one).
func exprText(src string, x ast.Expr) string {
	return src[x.Pos()-token.Pos(1) : x.End()-token.Pos(1)]
}
