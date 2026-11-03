// Package auxsign reports rules that read or move an immediate auxint
// with the wrong signedness.
package auxsign

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"math"
	"math/big"
	"slices"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/auxdomain/prior"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "auxsign",
	Doc: `report immediates and unsigned operands that a rule reads with the wrong signedness

An auxint is stored as a sign-extended int64, but the instruction need not
read it that way. An op whose auxint type is unsigned (UInt8) holds a
zero-extended immediate, and so does an op whose codegen zero-extends its
signed auxint: s390x/ssa.go emits CMPUconst's immediate as
int64(uint32(v.AuxInt)), so CMPUconst [-1] compares against 0xffffffff
(CLGFI's unsigned 32-bit immediate). Rules must use the immediate the way
the instruction does. Three mistakes are reported:

  - Reading a zero-extended immediate as signed. In

	(CMPUconst (SRDconst _ [c]) [n]) && c > 0 && c < 64 && (1<<uint(64-c)) <= uint64(n) => (FlagLT)

    uint64(n) sign-extends n. For n = -2147483648, which stands for
    0x80000000, it gives 0xffffffff80000000, so x>>1 < 0x80000000 folds to
    true. The fix is uint64(uint32(n)). Conversions of the auxint to a
    wider type and signed comparisons of it are reported unless the
    condition makes it non-negative.

  - Moving an immediate between ops that extend it differently, without
    a condition that makes the two agree. In

	(BRC {c} (CMPUconst x [y]) yes no) && y == int32(int8(y)) && ... => (CGIJ {c} x [int8(y)] yes no)

    y = -1 means 0xffffffff in CMPUconst but -1 (0xffffffffffffffff) in
    CGIJ, a signed 64-bit compare. Likewise, an unsigned imm8 c moved
    into makeValAndOff(int32(int8(c)), off) turns 200 into -56. The
    immediate's value is compared at the width of the destination's
    operation, so moving CMPWUconst's immediate into a 32-bit CIJ is fine.
    Only operand immediates are compared, not constants (MOVDconst [c]),
    whose width is their consumer's.

  - Comparing as signed a constant that a generic op reads as unsigned,
    such as a shift count. In

	(Lsh64x64 (And64 (Rsh64x64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c < e => (And64 (Lsh64x64 <t> x (Const64 <t2> [e-c])) (Const64 <t> [d<<e]))

    c = -1 is a shift by 2^64-1, which fills x with its sign bit, but
    c < e holds and the result shifts x left. A comparison is reported if
    it holds for a negative value the condition does not otherwise rule
    out, counting what earlier rules for the same op rule out.

Zero-extending ops are derived from the arch's codegen; see zeroExtended.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			return fmt.Errorf("%s: %v", set, err)
		}
		var zx map[string]uint
		if !set.Arch.Generic {
			zx = zeroExtended(pass.Ops.Dir, set.Arch.Name)
		}
		for _, r := range set.Rules {
			tr := res.Rule(r)
			if tr == nil {
				continue
			}
			c := &checker{pass: pass, res: res, info: res.Info, r: r, tr: tr, zx: zx}
			c.check()
		}
	}
	return nil
}

type checker struct {
	pass *analysis.Pass
	res  *typecheck.Result
	info *types.Info
	r    *rules.Rule
	tr   *typecheck.Rule
	zx   map[string]uint

	imms map[types.Object]imm
	f    *facts.Facts
}

// An imm is how an instruction uses an auxint.
type imm struct {
	op    string       // the op or block, such as "CMPUconst"
	arch  string       // its arch
	t     *types.Basic // the auxint's Go type
	zext  uint         // if nonzero, codegen zero-extends the low zext bits
	width uint         // the width of the operation that uses the immediate

	// operand reports whether the immediate is an operand of an
	// operation on the op's arguments, rather than a constant value
	// (MOVDconst [c], Const8 [c]), whose width is its consumer's.
	operand bool
}

// zero reports whether the immediate is zero-extended.
func (m imm) zero() bool { return m.zext != 0 || unsigned(m.t) }

// bits returns the number of auxint bits the instruction uses.
func (m imm) bits() uint {
	if m.zext != 0 {
		return m.zext
	}
	return width(m.t)
}

// value returns the value that the instruction uses for auxint x.
func (m imm) value(x *big.Int) *big.Int {
	return wrap(x, m.bits(), m.zero())
}

func (c *checker) check() {
	c.imms = map[types.Object]imm{}
	for name, occs := range c.r.MatchVars() {
		obj := c.tr.Vars[name]
		if obj == nil {
			continue
		}
		for _, o := range occs {
			if o.Kind != rules.OccAuxInt {
				continue
			}
			var node any = o.Value
			if o.Value == nil {
				node = c.r.MatchBlock
			}
			if m, ok := c.immOf(node, obj.Type()); ok {
				c.imms[obj] = m
			}
			break
		}
	}
	uo := unsignedOperands(c.r, c.tr)
	if len(c.imms) == 0 && (len(uo) == 0 || c.tr.Cond == nil) {
		return
	}
	c.f = prior.Facts(c.res, c.r, facts.New(c.res, c.r))
	if c.tr.Cond != nil && len(uo) > 0 {
		c.signedCompares(c.tr.Cond, true, uo)
	}
	if c.tr.Cond != nil {
		c.reads(c.tr.Cond)
	}
	c.eachResult(func(node any) {
		for _, fld := range []typecheck.Field{typecheck.AuxInt, typecheck.Aux, typecheck.Type} {
			if e := c.tr.Expr(node, fld); e != nil {
				c.reads(e)
			}
		}
		c.transfer(node)
	})
}

// eachResult calls fn for each result value and the result block.
func (c *checker) eachResult(fn func(node any)) {
	for _, v := range c.r.ResultValues() {
		v.Walk(func(v *rules.Value) bool {
			if !v.IsLeaf() {
				fn(v)
			}
			return true
		})
	}
	if c.r.ResultBlock != nil {
		fn(c.r.ResultBlock)
	}
}

// immOf returns the immediate of node (a *rules.Value or *rules.Block),
// whose auxint has Go type t.
func (c *checker) immOf(node any, t types.Type) (imm, bool) {
	b, ok := basicInt(t)
	if !ok {
		return imm{}, false
	}
	m := imm{t: b, width: 64}
	switch n := node.(type) {
	case *rules.Value:
		if n.Op == nil {
			return imm{}, false
		}
		m.op, m.arch = n.Op.Name, n.Op.Arch.Name
		if !n.Op.IsGeneric() {
			m.zext = c.zx[n.Op.Name]
		}
		m.width = narrow[m.arch][m.op]
		m.operand = n.Op.ArgLength != 0
	case *rules.Block:
		if n.Info == nil {
			return imm{}, false
		}
		m.op, m.arch = n.Info.Name, n.Info.Arch.Name
		m.width = narrow[m.arch][m.op]
		m.operand = true
	default:
		return imm{}, false
	}
	if m.width == 0 {
		m.width = 64
	}
	return m, true
}

// narrow gives the width of the operations that use the immediates of
// some ops and blocks, where it is less than 64 bits and the immediate
// is moved between ops that extend it differently.
//
// S390X: the 32-bit compares. CMPWconst and CMPWUconst assemble to CFI
// and CLFI, "COMPARE (LOGICAL) IMMEDIATE (32)", and CIJ and CLIJ are
// "COMPARE (LOGICAL) IMMEDIATE AND BRANCH RELATIVE (32<-8)"
// (cmd/internal/obj/s390x/asmz.go; S390XOps.go: "signed 32-bit integer
// comparison").
var narrow = map[string]map[string]uint{
	"S390X": {"CMPWconst": 32, "CMPWUconst": 32, "CIJ": 32, "CLIJ": 32},
}

// reads reports uses within e that read a zero-extended immediate as
// a signed value.
func (c *checker) reads(e ast.Expr) {
	ast.Inspect(e, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.CallExpr:
			id, m, ok := c.zeroExtVar(x.Args)
			if !ok || len(x.Args) != 1 {
				return true
			}
			to, ok := c.convType(x)
			if !ok || width(to) <= m.zext {
				return true
			}
			if c.nonneg(id, m) {
				return true
			}
			ex := c.negExample(id)
			c.pass.Reportf(c.r.Pos, "%s's auxint %s is zero-extended (%s codegen emits int64(uint%d(v.AuxInt))), but %s sign-extends it: %s=%s stands for %#x, not %#x; use %s(uint%d(%s))",
				m.op, id.Name, m.arch, m.zext, str(x), id.Name, ex, wrap(ex, m.zext, true), wrap(ex, 64, true), to, m.zext, id.Name)
		case *ast.BinaryExpr:
			switch x.Op {
			case token.LSS, token.LEQ, token.GTR, token.GEQ:
			default:
				return true
			}
			id, m, ok := c.zeroExtVar([]ast.Expr{x.X, x.Y})
			if !ok || c.nonneg(id, m) {
				return true
			}
			ex := c.negExample(id)
			c.pass.Reportf(c.r.Pos, "%s's auxint %s is zero-extended (%s codegen emits int64(uint%d(v.AuxInt))), but %s compares it as signed: %s=%s stands for %#x; compare uint%[4]d(%[6]s)",
				m.op, id.Name, m.arch, m.zext, str(x), id.Name, ex, wrap(ex, m.zext, true))
		}
		return true
	})
}

// zeroExtVar returns the first of es that is a match variable holding a
// signed auxint that codegen zero-extends.
func (c *checker) zeroExtVar(es []ast.Expr) (*ast.Ident, imm, bool) {
	for _, e := range es {
		id, ok := ast.Unparen(e).(*ast.Ident)
		if !ok {
			continue
		}
		m, ok := c.imms[c.info.Uses[id]]
		if ok && m.zext != 0 && !unsigned(m.t) {
			return id, m, true
		}
	}
	return nil, imm{}, false
}

// nonneg reports whether the condition makes id's value non-negative,
// so that sign- and zero-extension agree.
func (c *checker) nonneg(id *ast.Ident, m imm) bool {
	return c.f.In(id, 0, 1<<(m.zext-1)-1)
}

// negExample returns a negative value id may have: -1 if possible.
func (c *checker) negExample(id *ast.Ident) *big.Int {
	iv, _ := c.f.Range(id)
	if iv.Contains(-1) {
		return big.NewInt(-1)
	}
	return iv.Lo
}

// transfer reports node's auxint if it is a match variable's immediate,
// possibly converted, whose value differs in node's op.
func (c *checker) transfer(node any) {
	e := c.tr.Expr(node, typecheck.AuxInt)
	if e == nil {
		return
	}
	var dst imm
	var ok bool
	if call, isCall := ast.Unparen(e).(*ast.CallExpr); isCall && isMakeValAndOff(call) && len(call.Args) == 2 {
		// The Val of a ValAndOff is an int32 that codegen sign-extends
		// (ValAndOff.Val64).
		e = call.Args[0]
		dst, ok = c.immOf(node, types.Typ[types.Int32])
	} else {
		dst, ok = c.immOf(node, c.info.TypeOf(e))
	}
	if !ok {
		return
	}
	id, convs, ok := c.chain(e)
	if !ok {
		return
	}
	src, ok := c.imms[c.info.Uses[id]]
	if !ok || src.zero() == dst.zero() || !src.operand || !dst.operand {
		return
	}
	w := min(dst.width, 64)
	iv, _ := c.f.Range(id)
	for _, x := range samples(iv) {
		y := x
		for _, t := range slices.Backward(convs) {
			y = wrap(y, width(t), unsigned(t))
		}
		want, got := src.value(x), dst.value(y)
		if wrap(want, w, true).Cmp(wrap(got, w, true)) == 0 {
			continue
		}
		if c.refuted(id, x) {
			continue
		}
		c.pass.Reportf(c.r.Pos, "%s moves %s's %s immediate %s into %s, which %s it: %s=%s means %s in %s but %s in %s",
			str(e), src.op, extName(src), id.Name, dst.op, extVerb(dst), id.Name, x, hex(want, w), src.op, hex(got, w), dst.op)
		return
	}
}

func extName(m imm) string {
	if m.zero() {
		return "zero-extended"
	}
	return "sign-extended"
}

func extVerb(m imm) string {
	if m.zero() {
		return "zero-extends"
	}
	return "sign-extends"
}

// hex formats x as a w-bit two's complement value, in hex.
func hex(x *big.Int, w uint) string {
	return fmt.Sprintf("%#x", wrap(x, w, true))
}

// refuted reports whether the condition rules out id == x.
func (c *checker) refuted(id *ast.Ident, x *big.Int) bool {
	if !x.IsInt64() {
		return true
	}
	g := c.f.AssumeVar(id.Name, facts.Range(x.Int64(), x.Int64()))
	return g.In(id, 1, 0)
}

// chain returns the match variable that e converts, and the conversions,
// outermost first, if e is a variable or a chain of integer conversions
// of one.
func (c *checker) chain(e ast.Expr) (*ast.Ident, []*types.Basic, bool) {
	var convs []*types.Basic
	for {
		e = ast.Unparen(e)
		switch x := e.(type) {
		case *ast.Ident:
			return x, convs, true
		case *ast.CallExpr:
			t, ok := c.convType(x)
			if !ok || len(x.Args) != 1 {
				return nil, nil, false
			}
			convs = append(convs, t)
			e = x.Args[0]
		default:
			return nil, nil, false
		}
	}
}

// convType returns T if call is an integer conversion T(x).
func (c *checker) convType(call *ast.CallExpr) (*types.Basic, bool) {
	tv, ok := c.info.Types[call.Fun]
	if !ok || !tv.IsType() || len(call.Args) != 1 {
		return nil, false
	}
	if _, ok := basicInt(c.info.TypeOf(call.Args[0])); !ok {
		return nil, false
	}
	return basicInt(tv.Type)
}

func isMakeValAndOff(call *ast.CallExpr) bool {
	var name string
	switch f := call.Fun.(type) {
	case *ast.Ident:
		name = f.Name
	case *ast.SelectorExpr:
		name = f.Sel.Name
	}
	return name == "makeValAndOff" || name == "MakeValAndOff"
}

// samples returns values in iv at which the extensions and conversions
// of an immediate may disagree, most illustrative first.
func samples(iv facts.Interval) []*big.Int {
	var out []*big.Int
	add := func(x *big.Int) {
		if x == nil || !within(x, iv) {
			return
		}
		for _, y := range out {
			if y.Cmp(x) == 0 {
				return
			}
		}
		out = append(out, x)
	}
	add(big.NewInt(-1))
	for _, k := range []uint{7, 8, 15, 16, 31, 32, 63} {
		p := new(big.Int).Lsh(big.NewInt(1), k)
		for _, d := range []int64{0, -1} {
			add(new(big.Int).Add(p, big.NewInt(d)))
			add(new(big.Int).Sub(new(big.Int).Neg(p), big.NewInt(d)))
		}
	}
	add(iv.Lo)
	add(iv.Hi)
	add(big.NewInt(0))
	return out
}

func within(x *big.Int, iv facts.Interval) bool {
	return (iv.Lo == nil || iv.Lo.Cmp(x) <= 0) && (iv.Hi == nil || x.Cmp(iv.Hi) <= 0)
}

// wrap returns x reduced to w bits, as an unsigned or signed value.
func wrap(x *big.Int, w uint, unsigned bool) *big.Int {
	m := new(big.Int).Lsh(big.NewInt(1), w)
	y := new(big.Int).Mod(x, m)
	if !unsigned && y.Bit(int(w)-1) == 1 {
		y.Sub(y, m)
	}
	return y
}

func basicInt(t types.Type) (*types.Basic, bool) {
	if t == nil {
		return nil, false
	}
	b, ok := t.Underlying().(*types.Basic)
	if !ok || b.Info()&types.IsInteger == 0 {
		return nil, false
	}
	return b, true
}

func unsigned(b *types.Basic) bool { return b.Info()&types.IsUnsigned != 0 }

// width returns the width of integer type b; int, uint, and uintptr are
// taken to be 64 bits, as on every host that runs the compiler's tests.
func width(b *types.Basic) uint {
	switch b.Kind() {
	case types.Int8, types.Uint8:
		return 8
	case types.Int16, types.Uint16:
		return 16
	case types.Int32, types.Uint32:
		return 32
	}
	return 64
}

func str(e ast.Expr) string { return types.ExprString(e) }

// unsignedOperands returns the match variables of r that hold the auxint
// of a constant in an operand that a generic op reads as unsigned, such
// as c in (Rsh64Ux64 x (Const64 [c])), mapped to that op.
func unsignedOperands(r *rules.Rule, tr *typecheck.Rule) map[types.Object]*ops.Op {
	m := map[types.Object]*ops.Op{}
	for _, v := range r.MatchValues() {
		v.Walk(func(v *rules.Value) bool {
			if v.Op == nil || !v.Op.IsGeneric() {
				return true
			}
			sig, ok := opsig.Lookup(v.Op)
			if !ok || len(sig.Args) != len(v.Args) {
				return true
			}
			for i, a := range v.Args {
				if sig.Args[i].Kind != opsig.Int || sig.Args[i].Sign != opsig.Unsigned || a.Op == nil || !strings.HasPrefix(a.Op.Name, "Const") || !rules.IsVarText(a.AuxInt) {
					continue
				}
				if obj := tr.Vars[a.AuxInt]; obj != nil {
					m[obj] = v.Op
				}
			}
			return true
		})
	}
	return m
}

// signedCompares reports comparisons in e, a boolean expression assumed
// to have value truth, that hold for a negative uo variable: that is, for
// a huge unsigned operand that the comparison treats as small.
func (c *checker) signedCompares(e ast.Expr, truth bool, uo map[types.Object]*ops.Op) {
	switch x := ast.Unparen(e).(type) {
	case *ast.UnaryExpr:
		if x.Op == token.NOT {
			c.signedCompares(x.X, !truth, uo)
		}
	case *ast.BinaryExpr:
		var small ast.Expr
		switch x.Op {
		case token.LAND, token.LOR:
			c.signedCompares(x.X, truth, uo)
			c.signedCompares(x.Y, truth, uo)
			return
		case token.LSS, token.LEQ:
			small = x.X
			if !truth {
				small = x.Y
			}
		case token.GTR, token.GEQ:
			small = x.Y
			if !truth {
				small = x.X
			}
		default:
			return
		}
		id, ok := c.signedView(small)
		if !ok {
			return
		}
		op := uo[c.info.Uses[id]]
		if op == nil || c.f.In(id, 0, math.MaxInt64) {
			return
		}
		ex := c.negExample(id)
		w := width(c.basic(id))
		c.pass.Reportf(c.r.Pos, "%s reads %s as unsigned, but %s compares it as signed: %s=%s (%#x as a uint%d) satisfies it; compare uint%[7]d(%[4]s) or require %[4]s >= 0",
			op.Name, id.Name, str(x), id.Name, ex, wrap(ex, w, true), w)
	}
}

// signedView returns the variable that e is, possibly converted to a
// signed type at least as wide.
func (c *checker) signedView(e ast.Expr) (*ast.Ident, bool) {
	for {
		e = ast.Unparen(e)
		switch x := e.(type) {
		case *ast.Ident:
			return x, true
		case *ast.CallExpr:
			to, ok := c.convType(x)
			if !ok || unsigned(to) {
				return nil, false
			}
			from := c.basic(x.Args[0])
			if from == nil || unsigned(from) || width(to) < width(from) {
				return nil, false
			}
			e = x.Args[0]
		default:
			return nil, false
		}
	}
}

func (c *checker) basic(e ast.Expr) *types.Basic {
	b, _ := basicInt(c.info.TypeOf(e))
	return b
}
