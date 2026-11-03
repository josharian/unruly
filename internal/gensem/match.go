package gensem

import (
	"fmt"
	"go/ast"
	"go/types"
	"math"

	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// Matcher matches rules against values and builds their results, for one
// target configuration.
type Matcher struct {
	U   *Universe
	Cfg *Config
}

// NewMatcher returns a Matcher for cfg.
func NewMatcher(cfg *Config) *Matcher {
	return &Matcher{U: NewUniverse(cfg.PtrSize), Cfg: cfg}
}

// Invalid reports a result that violates an SSA invariant,
// such as a float constant holding a NaN.
type Invalid struct{ Msg string }

func (e *Invalid) Error() string { return "invalid result: " + e.Msg }

func (m *Matcher) typed(r *rules.Rule) (*typecheck.Result, *typecheck.Rule, error) {
	res, err := typecheck.Check(r.Set)
	if err != nil {
		return nil, nil, err
	}
	tr := res.Rule(r)
	if tr == nil {
		return nil, nil, fmt.Errorf("rule not type-checked")
	}
	if len(tr.Errors) > 0 {
		return nil, nil, unsupported("rule has type errors: %v", tr.Errors[0])
	}
	return res, tr, nil
}

// NewEnv returns an empty environment for r's expressions with root v.
func (m *Matcher) NewEnv(r *rules.Rule, v *Value) (*Env, *typecheck.Rule, error) {
	res, tr, err := m.typed(r)
	if err != nil {
		return nil, nil, err
	}
	return &Env{Info: res.Info, U: m.U, Cfg: m.Cfg, V: v, Vars: map[types.Object]GoVal{}}, tr, nil
}

// Match reports whether value rule r matches v, trying commutative
// argument orders and checking the condition exactly as rulegen's
// generated code does. If it matches, the Env holds the bindings.
//
// An error means the match could not be decided (*Unsupported), or that
// evaluating the condition panics (*Panic), which would crash the
// compiler.
func (m *Matcher) Match(r *rules.Rule, v *Value) (*Env, bool, error) {
	return m.match(r, v, true)
}

// Bind binds r's match variables to the parts of v in the written order
// of commutative args, ignoring the condition. It reports whether v has
// the shape of r's match.
func (m *Matcher) Bind(r *rules.Rule, v *Value) (*Env, bool, error) {
	return m.match(r, v, false)
}

func (m *Matcher) match(r *rules.Rule, v *Value, full bool) (*Env, bool, error) {
	if r.IsBlock() {
		return nil, false, unsupported("block rule")
	}
	env, tr, err := m.NewEnv(r, v)
	if err != nil {
		return nil, false, err
	}
	s := &matchState{env: env, tr: tr, full: full}
	ok, err := s.node(r.Match, v, func() (bool, error) {
		if !full || tr.Cond == nil {
			return true, nil
		}
		return env.EvalBool(tr.Cond)
	})
	if err != nil || !ok {
		return nil, false, err
	}
	return env, true, nil
}

type matchState struct {
	env  *Env
	tr   *typecheck.Rule
	full bool // try commuted orders
}

// bind binds name to g, or compares g against its earlier binding.
// It returns an undo function.
func (s *matchState) bind(name string, g GoVal) (ok bool, undo func()) {
	obj := s.tr.Vars[name]
	if obj == nil {
		return false, nil
	}
	if old, bound := s.env.Vars[obj]; bound {
		return goEqual(old, g), func() {}
	}
	g.T = obj.Type()
	s.env.Vars[obj] = g
	return true, func() { delete(s.env.Vars, obj) }
}

// node matches pattern p against v, then calls k to match the rest.
// As in rulegen's output, a commutative op's swapped order is tried only
// if the written order fails, including everything matched after it.
func (s *matchState) node(p *rules.Value, v *Value, k func() (bool, error)) (ok bool, err error) {
	var undos []func()
	defer func() {
		if ok {
			return // keep the bindings of a successful match
		}
		for i := len(undos) - 1; i >= 0; i-- {
			undos[i]()
		}
	}()
	bindName := func(name string, g GoVal) bool {
		ok, undo := s.bind(name, g)
		if undo != nil {
			undos = append(undos, undo)
		}
		return ok
	}
	if p.IsLeaf() {
		if p.Name == "_" {
			return k()
		}
		if !bindName(p.Name, GoVal{X: v}) {
			return false, nil
		}
		return k()
	}
	if v.Op != p.Op {
		return false, nil
	}
	if p.Op.ArgLength == -1 {
		if p.Rest && len(v.Args) < len(p.Args) || !p.Rest && len(v.Args) != len(p.Args) {
			return false, nil
		}
	}
	if p.Ellipsis {
		return k()
	}
	if p.Name != "" && !bindName(p.Name, GoVal{X: v}) {
		return false, nil
	}
	field := func(text string, f typecheck.Field, cur func(t types.Type) (GoVal, error)) (bool, error) {
		if text == "" || text == "_" {
			return true, nil
		}
		if rules.IsVarText(text) && s.tr.Vars[text] != nil {
			g, err := cur(s.tr.Vars[text].Type())
			if err != nil {
				return false, err
			}
			return bindName(text, g), nil
		}
		x := s.tr.Expr(p, f)
		if x == nil {
			return false, unsupported("match field %s", text)
		}
		want, err := s.env.Eval(x)
		if err != nil {
			return false, err
		}
		g, err := cur(want.T)
		if err != nil {
			return false, err
		}
		return goEqual(g, want), nil
	}
	if ok, err := field(p.Type, typecheck.Type, func(types.Type) (GoVal, error) { return GoVal{X: v.Type}, nil }); !ok || err != nil {
		return false, err
	}
	if ok, err := field(p.AuxInt, typecheck.AuxInt, func(t types.Type) (GoVal, error) { return auxIntGo(v, t) }); !ok || err != nil {
		return false, err
	}
	if p.Aux != "" && p.Aux != "_" {
		if p.Op.Aux != "Sym" {
			return false, unsupported("aux %s", p.Aux)
		}
		if ok, err := field(p.Aux, typecheck.Aux, func(types.Type) (GoVal, error) { return GoVal{X: v.Aux}, nil }); !ok || err != nil {
			return false, err
		}
	}
	orders := [][]*Value{v.Args}
	if s.full && p.Commutes() {
		orders = append(orders, append([]*Value{v.Args[1], v.Args[0]}, v.Args[2:]...))
	}
	for _, args := range orders {
		ok, err := s.args(p.Args, args, k)
		if ok || err != nil {
			return ok, err
		}
	}
	return false, nil
}

func (s *matchState) args(ps []*rules.Value, vs []*Value, k func() (bool, error)) (bool, error) {
	if len(ps) == 0 {
		return k()
	}
	return s.node(ps[0], vs[0], func() (bool, error) { return s.args(ps[1:], vs[1:], k) })
}

// auxIntGo converts v's AuxInt to Go type t as rulegen's auxIntToX does.
func auxIntGo(v *Value, t types.Type) (GoVal, error) {
	switch v.Op.AuxIntType {
	case "float32", "float64":
		return mkFloat(t, math.Float64frombits(uint64(v.AuxInt))), nil
	case "bool":
		return mkBool(t, v.AuxInt != 0), nil
	}
	switch basicInfo(t) {
	case infoInt:
		return mkInt(t, uint64(v.AuxInt)), nil
	case infoBool:
		return mkBool(t, v.AuxInt != 0), nil
	}
	return GoVal{}, unsupported("auxint type %s", v.Op.AuxIntType)
}

// encodeAuxInt converts g to an AuxInt for op's auxint type, as rulegen's
// xToAuxInt does.
func encodeAuxInt(auxType string, g GoVal) (int64, error) {
	switch auxType {
	case "float32", "float64":
		if math.IsNaN(g.F) {
			return 0, &Invalid{"float constant is NaN"}
		}
		return int64(math.Float64bits(g.F)), nil
	case "bool":
		return int64(g.I & 1), nil
	case "int8", "uint8":
		return int64(int8(g.I)), nil
	case "int16":
		return int64(int16(g.I)), nil
	case "int32":
		return int64(int32(g.I)), nil
	case "int64":
		return int64(g.I), nil
	}
	return 0, unsupported("auxint type %s", auxType)
}

// goEqual reports whether a == b in Go.
func goEqual(a, b GoVal) bool {
	if a.X != nil || b.X != nil {
		return sameRef(a.X, b.X)
	}
	switch basicInfo(a.T) {
	case infoInt, infoBool:
		return a.I == b.I
	case infoFloat:
		return a.F == b.F
	case infoString:
		return a.S == b.S
	}
	return sameRef(a.X, b.X)
}

// Build builds the result of r, which matched with bindings env.
func (m *Matcher) Build(r *rules.Rule, env *Env) (*Value, error) {
	if r.ResultCode != "" {
		return nil, unsupported("{code} result")
	}
	_, tr, err := m.typed(r)
	if err != nil {
		return nil, err
	}
	if r.Result.Ellipsis {
		nv := *env.V
		nv.Op = r.Result.Op
		return &nv, nil
	}
	// rulegen declares the names of result sub-expressions before
	// filling them in, so create every value first.
	shells := map[*rules.Value]*Value{}
	var create func(rv *rules.Value)
	create = func(rv *rules.Value) {
		if rv.IsLeaf() {
			return
		}
		nv := &Value{Op: rv.Op, Uses: 1}
		shells[rv] = nv
		if rv.Name != "" && rv != r.Result {
			if obj := tr.Vars[rv.Name]; obj != nil {
				env.Vars[obj] = GoVal{T: obj.Type(), X: nv}
			}
		}
		for _, a := range rv.Args {
			create(a)
		}
	}
	create(r.Result)
	var fill func(rv *rules.Value) (*Value, error)
	fill = func(rv *rules.Value) (*Value, error) {
		if rv.IsLeaf() {
			x := tr.Expr(rv, typecheck.Name)
			if x == nil {
				return nil, unsupported("result leaf %s", rv.Name)
			}
			g, err := env.Eval(x)
			if err != nil {
				return nil, err
			}
			v, ok := g.X.(*Value)
			if !ok || v == nil {
				return nil, unsupported("result leaf %s is not a value", rv.Name)
			}
			return v, nil
		}
		nv := shells[rv]
		switch typ, src := r.ResultType(rv); src {
		case rules.TypeExplicit:
			g, err := env.Eval(tr.Expr(rv, typecheck.Type))
			if err != nil {
				return nil, err
			}
			t, _ := g.X.(*Type)
			if t == nil {
				return nil, unsupported("result type %s", typ)
			}
			nv.Type = t
		case rules.TypeInherited:
			nv.Type = env.V.Type
		case rules.TypeOpDefault:
			nv.Type = m.U.Named(typ)
			if nv.Type == nil {
				return nil, unsupported("default type %q of %s", typ, rv.Op)
			}
		}
		if rv.AuxInt != "" {
			x := tr.Expr(rv, typecheck.AuxInt)
			if x == nil {
				return nil, unsupported("result auxint %s", rv.AuxInt)
			}
			g, err := env.Eval(x)
			if err != nil {
				return nil, err
			}
			ai, err := encodeAuxInt(rv.Op.AuxIntType, g)
			if err != nil {
				return nil, err
			}
			nv.AuxInt = ai
		}
		if rv.Aux != "" {
			g, err := env.Eval(tr.Expr(rv, typecheck.Aux))
			if err != nil {
				return nil, err
			}
			sym, ok := g.X.(*Sym)
			if rv.Op.Aux != "Sym" || !ok {
				return nil, unsupported("result aux %s", rv.Aux)
			}
			nv.Aux = sym
		}
		for _, a := range rv.Args {
			av, err := fill(a)
			if err != nil {
				return nil, err
			}
			nv.Args = append(nv.Args, av)
		}
		return nv, nil
	}
	return fill(r.Result)
}

// Conjuncts returns the top-level && operands of x.
func Conjuncts(x ast.Expr) []ast.Expr {
	switch y := x.(type) {
	case *ast.ParenExpr:
		return Conjuncts(y.X)
	case *ast.BinaryExpr:
		if y.Op.String() == "&&" {
			return append(Conjuncts(y.X), Conjuncts(y.Y)...)
		}
	}
	if x == nil {
		return nil
	}
	return []ast.Expr{x}
}
