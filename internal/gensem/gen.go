package gensem

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"math"
	"math/rand/v2"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// Gen generates random value trees shaped like a rule's match.
//
// The trees are well-typed generic SSA. Leaves are opaque values or,
// sometimes, constants or small trees that helpers like isNonNegative
// recognize, such as (ZeroExt8to64 x). Opaque pointers may point into the
// variables that Addr and LocalAddr name. Integers favor values that
// occur in the rule and their neighbors, powers of two and their
// neighbors, and the extremes of each width, so that conditions like
// c < 64 are satisfied and probed at their edges; equality conjuncts like
// d == 64-c are solved for d.
type Gen struct {
	Rand    *rand.Rand
	Matcher *Matcher
	Generic *ops.Arch // for the Const ops that leaves may become
	Pool    []int64

	// per tree
	values map[string]*Value
	named  []*Value // values, in order of generation
	types  map[string]*Type
	auxes  map[string]int64
	syms   map[string]*Sym // by variable
	objs   map[int]*Sym    // by object
	nodes  map[*rules.Value]*Value
	env    *Env
	tr     *typecheck.Rule
}

// RulePool returns the integer constants in r's expressions, for Gen.Pool.
func RulePool(r *rules.Rule) []int64 {
	res, err := typecheck.Check(r.Set)
	if err != nil {
		return nil
	}
	tr := res.Rule(r)
	if tr == nil {
		return nil
	}
	var pool []int64
	visit := func(x ast.Expr) {
		if x == nil {
			return
		}
		ast.Inspect(x, func(n ast.Node) bool {
			if e, ok := n.(ast.Expr); ok {
				if tv := res.Info.Types[e]; tv.Value != nil && tv.Value.Kind() == constant.Int {
					if i, ok := constant.Int64Val(tv.Value); ok {
						pool = append(pool, i)
					} else if u, ok := constant.Uint64Val(tv.Value); ok {
						pool = append(pool, int64(u))
					}
				}
			}
			return true
		})
	}
	visit(tr.Cond)
	r.Match.Walk(func(v *rules.Value) bool {
		visit(tr.Expr(v, typecheck.AuxInt))
		return true
	})
	if r.Result != nil {
		r.Result.Walk(func(v *rules.Value) bool {
			visit(tr.Expr(v, typecheck.AuxInt))
			return true
		})
	}
	return pool
}

// Generate returns a random value tree with the shape of r's match, with
// commutative args in written order. Generate uses the shape and the
// constant parts of the match; Matcher.Match decides whether the tree
// actually matches.
func (g *Gen) Generate(r *rules.Rule) (*Value, error) {
	env, tr, err := g.Matcher.NewEnv(r, nil)
	if err != nil {
		return nil, err
	}
	g.env, g.tr = env, tr
	g.values = map[string]*Value{}
	g.named = nil
	g.types = map[string]*Type{}
	g.auxes = map[string]int64{}
	g.syms = map[string]*Sym{}
	g.objs = map[int]*Sym{}
	g.nodes = map[*rules.Value]*Value{}
	v, err := g.gen(r.Match, constraint{})
	if err != nil {
		return nil, err
	}
	g.Solve(r, v)
	return v, nil
}

// constraint describes the type a parent requires of an arg.
type constraint struct {
	exact   *Type
	kind    opsig.Kind // Unknown means anything
	width   int        // in bits; 0 means any
	ptrSize int64      // for Ptr: a pointer-sized integer is also a pointer
}

func (c constraint) admits(t *Type) bool {
	if c.exact != nil {
		return t == c.exact
	}
	if c.width != 0 && t.Bits() != c.width {
		return false
	}
	switch c.kind {
	case opsig.Int:
		return t.IsInteger()
	case opsig.Float:
		return t.IsFloat()
	case opsig.Bool:
		return t.IsBoolean()
	case opsig.Flags:
		return t.IsFlags()
	case opsig.Tuple:
		return t.IsTuple()
	case opsig.Ptr:
		// SSA does not keep pointers and pointer-sized integers apart
		// (see opsig.Ptr).
		return t.IsPtr() || t.IsInteger() && t.Size == c.ptrSize
	case opsig.Mem:
		return t.IsMemory()
	case opsig.Unknown, opsig.Any:
		return true
	}
	return false
}

func (g *Gen) randIntType(size int64) *Type {
	if size == 0 {
		sizes := []int64{1, 2, 4, 8, g.Matcher.U.PtrSize}
		size = sizes[g.Rand.IntN(len(sizes))]
	}
	return g.Matcher.U.Int(size, g.Rand.IntN(2) == 0)
}

// choose returns a type satisfying c.
func (g *Gen) choose(c constraint) *Type {
	if c.exact != nil {
		return c.exact
	}
	u := g.Matcher.U
	switch c.kind {
	case opsig.Int, opsig.Unknown, opsig.Any:
		if c.kind != opsig.Int && g.Rand.IntN(4) == 0 {
			// Any scalar.
			switch g.Rand.IntN(3) {
			case 0:
				return u.Named("Bool")
			case 1:
				return u.Named("Float64")
			default:
				return u.Named("Float32")
			}
		}
		return g.randIntType(int64(c.width / 8))
	case opsig.Float:
		if c.width == 32 {
			return u.Named("Float32")
		}
		if c.width == 64 {
			return u.Named("Float64")
		}
		return u.Named("Float64")
	case opsig.Bool:
		return u.Named("Bool")
	case opsig.Flags:
		return u.Named("Flags")
	case opsig.Ptr:
		if g.Rand.IntN(2) == 0 {
			return u.Named("BytePtr")
		}
		return u.Named("Int64Ptr")
	case opsig.Mem:
		return u.Named("Mem")
	}
	return nil
}

// natural returns the constraint that op itself puts on its result.
func (g *Gen) natural(op *ops.Op) (constraint, bool) {
	sig, ok := opsig.Lookup(op)
	if !ok || sig.SIMD {
		return constraint{}, false
	}
	return g.operandConstraint(sig.Result), true
}

func (g *Gen) operandConstraint(o opsig.Operand) constraint {
	switch o.Kind {
	case opsig.Int, opsig.Float, opsig.Bool, opsig.Flags, opsig.Tuple:
		return constraint{kind: o.Kind, width: o.Width}
	case opsig.Ptr, opsig.Mem:
		return constraint{kind: o.Kind, ptrSize: g.Matcher.U.PtrSize}
	case opsig.Any:
		return constraint{kind: opsig.Any}
	}
	return constraint{kind: o.Kind, width: -1} // unmodeled
}

func (g *Gen) gen(p *rules.Value, c constraint) (*Value, error) {
	if c.width < 0 {
		return nil, unsupported("operand kind")
	}
	if p.IsLeaf() {
		if p.Name != "_" {
			if v := g.values[p.Name]; v != nil {
				if !c.admits(v.Type) {
					return nil, unsupported("inconsistent types for %s", p.Name)
				}
				return v, nil
			}
		}
		if c.kind == opsig.Tuple {
			return nil, unsupported("tuple leaf")
		}
		if p.Name != "_" && g.Rand.IntN(8) == 0 {
			// Sometimes, two variables are the same value, as
			// conditions like isSamePtr(p1, p2) require.
			if v := g.reuse(c); v != nil {
				v.Uses++
				g.values[p.Name] = v
				g.nodes[p] = v
				return v, nil
			}
		}
		t := g.choose(c)
		if t == nil {
			return nil, unsupported("leaf type")
		}
		v := g.leaf(t)
		if p.Name != "_" {
			v.Name = p.Name
			g.values[p.Name] = v
			g.named = append(g.named, v)
		}
		g.nodes[p] = v
		return v, nil
	}
	if p.Rest || p.Op.ArgLength < 0 {
		return nil, unsupported("variadic op %s", p.Op)
	}
	if p.Op.Aux != "Sym" && p.Aux != "" && p.Aux != "_" {
		return nil, unsupported("aux")
	}
	sig, ok := opsig.Lookup(p.Op)
	if !ok || sig.SIMD {
		return nil, unsupported("op %s", p.Op)
	}

	// The node's type.
	var t *Type
	switch {
	case p.Type != "" && p.Type != "_" && rules.IsVarText(p.Type) && g.types[p.Type] != nil:
		t = g.types[p.Type]
	case p.Type != "" && p.Type != "_" && !rules.IsVarText(p.Type):
		x := g.tr.Expr(p, typecheck.Type)
		if x == nil {
			return nil, unsupported("match type %s", p.Type)
		}
		gv, err := g.env.Eval(x)
		if err != nil {
			return nil, err
		}
		t, _ = gv.X.(*Type)
	}
	nat := g.operandConstraint(sig.Result)
	if nat.width < 0 {
		return nil, unsupported("result kind of %s", p.Op)
	}
	if def := g.Matcher.U.Named(p.Op.Typ); t == nil && def != nil && c.admits(def) && (def.IsTuple() || nat.admits(def)) && g.Rand.IntN(4) != 0 {
		// Usually, a value has its op's default type.
		t = def
	}
	if t == nil && (p.Op.Name == "Select0" || p.Op.Name == "Select1") && len(p.Args) == 1 && !p.Args[0].IsLeaf() {
		// A Select's type is its tuple's element type.
		tv, err := g.gen(p.Args[0], constraint{kind: opsig.Tuple})
		if err != nil {
			return nil, err
		}
		et := tv.Type.Elems[0]
		if p.Op.Name == "Select1" {
			et = tv.Type.Elems[1]
		}
		if !c.admits(et) {
			return nil, unsupported("inconsistent type for %s", p.Op)
		}
		v := &Value{Op: p.Op, Type: et, Uses: int32(1 + g.Rand.IntN(2)), Args: []*Value{tv}}
		g.nodes[p] = v
		if rules.IsVarText(p.Type) {
			g.types[p.Type] = et
		}
		if p.Name != "" {
			g.values[p.Name] = v
		}
		return v, nil
	}
	if t == nil {
		switch {
		case nat.kind == opsig.Tuple:
			et := make([]*Type, 2)
			for i, e := range sig.Result.Elems {
				// Tuples come from ssagen, which types them as
				// the op interprets them: Div128u gives (uint64, uint64).
				et[i] = g.choose(g.operandConstraint(e))
				if et[i] != nil && et[i].IsInteger() && e.Sign != opsig.SignAny {
					et[i] = g.Matcher.U.Int(et[i].Size, e.Sign == opsig.Signed)
				}
				if et[i] == nil {
					return nil, unsupported("tuple element")
				}
			}
			t = g.Matcher.U.Tuple(et[0], et[1])
		case c.exact != nil:
			t = c.exact
		case nat.kind == opsig.Any:
			// CondSelect, Copy: the type of an arg that fixes its own.
			for i, a := range p.Args {
				if i < len(sig.Args) && sig.Args[i].Kind == opsig.Any && !a.IsLeaf() {
					if an, ok := g.natural(a.Op); ok && an.kind != opsig.Any && an.kind != opsig.Unknown && (an.width > 0 || an.kind == opsig.Bool) {
						t = g.choose(an)
						break
					}
				}
			}
			if t == nil {
				t = g.choose(c)
			}
		case nat.width == 0 && nat.kind == opsig.Int && c.width == 0:
			// Ctz64 and friends: int.
			t = g.Matcher.U.Int(g.Matcher.U.PtrSize, g.Rand.IntN(2) == 0)
		default:
			if nat.width == 0 {
				nat.width = c.width
			}
			t = g.choose(nat)
		}
	}
	if t == nil || !c.admits(t) || t.Kind != TTuple && !nat.admits(t) {
		return nil, unsupported("inconsistent type for %s", p.Op)
	}
	if rules.IsVarText(p.Type) {
		g.types[p.Type] = t
	}

	v := &Value{Op: p.Op, Type: t, Uses: int32(1 + g.Rand.IntN(2))}
	g.nodes[p] = v
	if p.Name != "" {
		if g.values[p.Name] != nil {
			return nil, unsupported("repeated name %s", p.Name)
		}
		g.values[p.Name] = v
	}

	if p.Op.Aux == "Sym" {
		switch {
		case rules.IsVarText(p.Aux) && g.syms[p.Aux] != nil:
			v.Aux = g.syms[p.Aux]
		case p.Aux == "" || p.Aux == "_" || rules.IsVarText(p.Aux):
			v.Aux = g.sym(p.Op.Name == "LocalAddr")
			if rules.IsVarText(p.Aux) {
				g.syms[p.Aux] = v.Aux.(*Sym)
			}
		default:
			return nil, unsupported("aux %s", p.Aux)
		}
	}
	if p.Op.HasAuxInt {
		switch {
		case rules.IsVarText(p.AuxInt):
			if a, ok := g.auxes[p.AuxInt]; ok {
				v.AuxInt = a
			} else {
				v.AuxInt = g.randAux(p.Op, t)
				g.auxes[p.AuxInt] = v.AuxInt
			}
		case p.AuxInt != "" && p.AuxInt != "_":
			x := g.tr.Expr(p, typecheck.AuxInt)
			if tv, ok := g.env.Info.Types[x]; ok && tv.Value != nil {
				gv, err := fromConstant(tv.Value, tv.Type)
				if err != nil {
					return nil, err
				}
				if basicInfo(gv.T) == infoFloat && gv.F == 0 && g.Rand.IntN(2) == 0 {
					// [0] matches -0 too, since rulegen compares with ==.
					gv.F = math.Copysign(0, -1)
				}
				if v.AuxInt, err = encodeAuxInt(p.Op.AuxIntType, gv); err != nil {
					return nil, err
				}
			} else {
				v.AuxInt = g.randAux(p.Op, t)
			}
		default:
			v.AuxInt = g.randAux(p.Op, t)
		}
	}

	// Args. Width-0 integer operands (IsInBounds) share one type, as do
	// Any operands and an Any result (CondSelect).
	pargs := p.Args
	if p.Ellipsis {
		// (Op ...): any args.
		pargs = make([]*rules.Value, p.Op.ArgLength)
		for i := range pargs {
			pargs[i] = &rules.Value{Text: "_", Name: "_"}
		}
	}
	var shared *Type
	for i, a := range pargs {
		ac := g.operandConstraint(sig.Args[i])
		switch {
		case ac.kind == opsig.Any:
			ac = constraint{exact: t}
		case ac.kind == opsig.Int && ac.width == 0 && sig.Result.Kind == opsig.Ptr:
			// AddPtr's and PtrIndex's index is an int.
			ac = constraint{exact: g.Matcher.U.Int(g.Matcher.U.PtrSize, g.Rand.IntN(2) == 0)}
		case ac.kind == opsig.Int && ac.width == 0 && sig.Result.Kind == opsig.Bool:
			if shared == nil {
				shared = g.sharedType(pargs, sig)
			}
			ac = constraint{exact: shared}
		}
		av, err := g.gen(a, ac)
		if err != nil {
			return nil, err
		}
		v.Args = append(v.Args, av)
	}
	if p.Name != "" {
		g.named = append(g.named, v) // complete, so reusable
	}
	return v, nil
}

// reuse returns a random complete value already bound to a variable,
// whose type satisfies c, or nil.
func (g *Gen) reuse(c constraint) *Value {
	var vs []*Value
	for _, v := range g.named {
		if v.Type != nil && !v.Type.IsMemory() && c.admits(v.Type) {
			vs = append(vs, v)
		}
	}
	if len(vs) == 0 {
		return nil
	}
	return vs[g.Rand.IntN(len(vs))]
}

// sharedType picks the type of the width-0 integer args of a comparison
// like IsInBounds, honoring any arg op that fixes its width.
func (g *Gen) sharedType(args []*rules.Value, sig opsig.Sig) *Type {
	for i, a := range args {
		if sig.Args[i].Kind != opsig.Int || sig.Args[i].Width != 0 {
			continue
		}
		if !a.IsLeaf() {
			if nat, ok := g.natural(a.Op); ok && nat.kind == opsig.Int && nat.width > 0 {
				return g.randIntType(int64(nat.width / 8))
			}
		}
	}
	return g.Matcher.U.Int(g.Matcher.U.PtrSize, g.Rand.IntN(2) == 0)
}

// Objects: globals are 1-3 and locals 11-13 (a global and a local are
// never the same variable). An opaque pointer may point into any of
// them, or into object 21, which no symbol names.
func (g *Gen) sym(local bool) *Sym {
	obj := 1 + g.Rand.IntN(3)
	if local {
		obj += 10
	}
	if s := g.objs[obj]; s != nil {
		return s
	}
	s := &Sym{Obj: obj, Local: local}
	g.objs[obj] = s
	return s
}

// leaf returns an opaque value of type t or, sometimes, a constant.
func (g *Gen) leaf(t *Type) *Value {
	if (t.IsInteger() || t.IsBoolean()) && g.Generic != nil && g.Rand.IntN(8) == 0 {
		if v := g.shaped(t); v != nil {
			return v
		}
	}
	v := &Value{Type: t}
	switch {
	case t.IsInteger():
		v.Leaf = IntVal(t.Bits(), uint64(g.Int(t.Bits())))
	case t.IsFloat():
		v.Leaf = FloatVal(t.Bits(), g.Float())
	case t.IsBoolean():
		v.Leaf = BoolVal(g.Rand.IntN(2) == 0)
	case t.IsFlags():
		v.Leaf = Val{Kind: KFlags, Bits: uint64(g.Rand.IntN(2))}
	case t.IsMemory():
		v.Leaf = Val{Kind: KMem}
		return v
	case t.IsPtr():
		w := t.Bits()
		var off uint64
		switch g.Rand.IntN(8) {
		case 0, 1, 2, 3:
		case 4, 5, 6:
			off = uint64(8 * g.Rand.IntN(4))
		default:
			off = uint64(g.Int(w))
		}
		base := []int{0, 1, 2, 3, 11, 12, 13, 21}[g.Rand.IntN(8)]
		if base == 0 && g.Rand.IntN(2) == 0 {
			off = 0
		}
		v.Leaf = PtrVal(w, base, off)
		if base == 0 && off == 0 && g.Generic != nil && g.Rand.IntN(2) == 0 {
			if op := g.Generic.Op("ConstNil"); op != nil {
				return &Value{Op: op, Type: t, Uses: 1}
			}
		}
		return v
	}
	if g.Rand.IntN(4) != 0 || g.Generic == nil {
		return v
	}
	var name string
	switch {
	case t.IsInteger():
		name = "Const" + itoa(t.Bits())
		v.AuxInt = v.Leaf.Int()
	case t.IsFloat() && !math.IsNaN(v.Leaf.Float()):
		name = "Const" + itoa(t.Bits()) + "F"
		v.AuxInt = int64(math.Float64bits(v.Leaf.Float()))
	case t.IsBoolean():
		name = "ConstBool"
		v.AuxInt = int64(v.Leaf.Bits)
	default:
		return v
	}
	v.Op = g.Generic.Op(name)
	if v.Op == nil {
		return &Value{Type: t, Leaf: v.Leaf}
	}
	v.Leaf = Val{}
	v.Uses = 1
	return v
}

// shaped returns a small value tree of integer type t whose form
// conditions like isNonNegative recognize, such as (ZeroExt8to64 x) or
// (Rsh64Ux64 x (Const64 [3])), or nil.
func (g *Gen) shaped(t *Type) *Value {
	w := t.Bits()
	op := func(name string) *ops.Op { return g.Generic.Op(name) }
	leaf := func(t *Type) *Value { return &Value{Type: t, Leaf: IntVal(t.Bits(), uint64(g.Int(t.Bits())))} }
	konst := func(w int, c int64) *Value {
		return &Value{Op: op("Const" + itoa(w)), Type: g.Matcher.U.Int(int64(w/8), true), AuxInt: sext(uint64(c), w), Uses: 1}
	}
	if t.IsBoolean() {
		// A comparison.
		aw := []int{8, 16, 32, 64}[g.Rand.IntN(4)]
		name := []string{"Eq", "Neq", "Less", "Leq"}[g.Rand.IntN(4)] + itoa(aw)
		at := g.Matcher.U.Int(int64(aw/8), g.Rand.IntN(2) == 0)
		o := op(name)
		if o == nil {
			return nil
		}
		return &Value{Op: o, Type: t, Uses: 1, Args: []*Value{leaf(at), leaf(at)}}
	}
	var v *Value
	switch g.Rand.IntN(4) {
	case 0: // extension
		var froms []int
		for _, f := range []int{8, 16, 32} {
			if f < w {
				froms = append(froms, f)
			}
		}
		if len(froms) == 0 {
			return nil
		}
		f := froms[g.Rand.IntN(len(froms))]
		kind := "ZeroExt"
		if g.Rand.IntN(2) == 0 {
			kind = "SignExt"
		}
		v = &Value{Op: op(fmt.Sprintf("%s%dto%d", kind, f, w)), Args: []*Value{leaf(g.Matcher.U.Int(int64(f/8), kind == "SignExt"))}}
	case 1: // mask
		v = &Value{Op: op("And" + itoa(w)), Args: []*Value{leaf(t), konst(w, g.Int(w))}}
	case 2: // shift right
		if w < 32 {
			return nil
		}
		name := fmt.Sprintf("Rsh%dUx64", w)
		if g.Rand.IntN(2) == 0 {
			name = fmt.Sprintf("Rsh%dx64", w)
		}
		v = &Value{Op: op(name), Args: []*Value{leaf(t), konst(64, int64(g.Rand.IntN(w)))}}
	case 3: // count
		if t.Size != g.Matcher.U.PtrSize {
			return nil
		}
		n := []string{"Ctz", "BitLen"}[g.Rand.IntN(2)]
		aw := []int{8, 16, 32, 64}[g.Rand.IntN(4)]
		v = &Value{Op: op(n + itoa(aw)), Args: []*Value{leaf(g.Matcher.U.Int(int64(aw/8), false))}}
	}
	if v.Op == nil {
		return nil
	}
	v.Type, v.Uses = t, 1
	return v
}

func itoa(n int) string {
	return map[int]string{8: "8", 16: "16", 32: "32", 64: "64"}[n]
}

func (g *Gen) randAux(op *ops.Op, t *Type) int64 {
	if op.Name == "OffPtr" {
		// An offset into an object, so much smaller than the address
		// space: the sum of two offsets fits in a pointer. (OffPtr
		// [1<<32] p) is p on a 32-bit target, but never occurs.
		return g.Int(int(g.Matcher.U.PtrSize*8) - 2)
	}
	switch op.AuxIntType {
	case "bool":
		// For shifts and divisions, a promise about the args.
		if g.Rand.IntN(4) == 0 {
			return 1
		}
		return 0
	case "int8":
		return int64(int8(g.Int(8)))
	case "int16":
		return int64(int16(g.Int(16)))
	case "int32":
		return int64(int32(g.Int(32)))
	case "int64":
		return g.Int(64)
	case "uint8":
		return int64(int8(g.Int(8)))
	case "float32":
		for {
			f := float32(g.Float())
			if f == f {
				return int64(math.Float64bits(float64(f)))
			}
		}
	case "float64":
		for {
			f := g.Float()
			if f == f {
				return int64(math.Float64bits(f))
			}
		}
	}
	return 0
}

// Int returns an interesting w-bit integer, sign-extended.
func (g *Gen) Int(w int) int64 {
	r := g.Rand
	var x int64
	switch p := r.IntN(100); {
	case p < 25:
		x = int64(r.IntN(141) - 70)
	case p < 40:
		x = int64(1) << uint(r.IntN(w))
		switch r.IntN(4) {
		case 0:
			x--
		case 1:
			x = -x
		case 2:
			x++
		}
	case p < 50:
		c := []int64{0, 1, -1, 2, -2, math.MinInt64 >> (64 - uint(w)), math.MaxInt64 >> (64 - uint(w)), 3, 5, 7, 10, 255, 256, 65535, 1 << 31, 1<<32 - 1}
		x = c[r.IntN(len(c))]
	case p < 75 && len(g.Pool) > 0:
		x = g.Pool[r.IntN(len(g.Pool))]
		switch r.IntN(8) {
		case 0:
			x++
		case 1:
			x--
		case 2:
			x = -x
		case 3:
			x = ^x
		}
	default:
		x = int64(r.Uint64())
		if r.IntN(2) == 0 {
			x >>= uint(r.IntN(64))
		}
	}
	return sext(uint64(x), w)
}

// Float returns an interesting float64.
func (g *Gen) Float() float64 {
	r := g.Rand
	switch p := r.IntN(100); {
	case p < 5:
		// Signed zeros are the commonest float edge case.
		return math.Copysign(0, float64(r.IntN(2))-0.5)
	case p < 30:
		c := []float64{0, math.Copysign(0, -1), 1, -1, 2, 0.5, -0.5, math.Inf(1), math.Inf(-1), math.NaN(),
			math.MaxFloat64, -math.MaxFloat64, math.SmallestNonzeroFloat64, 1 << 31, -(1 << 31), 1 << 63, -(1 << 63),
			1 << 32, 1 << 53, 1<<53 + 1, 3, 0.25, 1.5, 2.5, -2.5, math.MaxFloat32, 1e300, 4294967295, 9223372036854775807, 0.1}
		return c[r.IntN(len(c))]
	case p < 55:
		return float64(r.IntN(201) - 100)
	case p < 70:
		return float64(r.IntN(41)-20) / 4
	case p < 80 && len(g.Pool) > 0:
		return float64(g.Pool[r.IntN(len(g.Pool))])
	}
	return math.Float64frombits(r.Uint64())
}

// Solve adjusts auxints in root, the tree most recently generated for r,
// so that equality conjuncts of r's condition of the form c == expr hold,
// where c is a match auxint variable.
func (g *Gen) Solve(r *rules.Rule, root *Value) {
	if g.tr.Cond == nil {
		return
	}
	occs := r.MatchVars()
	for range 2 {
		for _, conj := range Conjuncts(g.tr.Cond) {
			be, ok := conj.(*ast.BinaryExpr)
			if !ok || be.Op != token.EQL {
				continue
			}
			for _, side := range [][2]ast.Expr{{be.X, be.Y}, {be.Y, be.X}} {
				id, ok := unparen(side[0]).(*ast.Ident)
				if !ok {
					continue
				}
				os := occs[id.Name]
				if len(os) == 0 || os[0].Kind != rules.OccAuxInt {
					continue
				}
				env, ok, err := g.Matcher.Bind(r, root)
				if err != nil || !ok {
					return
				}
				gv, err := env.Eval(side[1])
				if err != nil {
					continue
				}
				if want := g.env.Info.TypeOf(side[0]); want != nil && basicInfo(gv.T) == infoInt && basicInfo(want) == infoInt {
					gv = mkInt(want, gv.I)
				}
				for _, o := range os {
					n := g.nodes[o.Value]
					if n == nil || n.Op == nil {
						continue
					}
					if a, err := encodeAuxInt(n.Op.AuxIntType, gv); err == nil {
						n.AuxInt = a
					}
				}
				break
			}
		}
	}
}

func unparen(x ast.Expr) ast.Expr {
	for {
		p, ok := x.(*ast.ParenExpr)
		if !ok {
			return x
		}
		x = p.X
	}
}
