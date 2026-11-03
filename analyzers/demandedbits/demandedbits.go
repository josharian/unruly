// Package demandedbits reports rules whose result reads bits of a value
// that the matched pattern ignores.
package demandedbits

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/types"
	"math/bits"
	"sort"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "demandedbits",
	Doc: `report rules whose result depends on bits that the match ignores

A narrow SSA value lives in a wider register whose upper bits are
undefined: an int8 is only its low 8 bits. So a rule's result must not
depend on bits of a matched value that the matched expression does not
depend on. For example, MIPS.rules has

	(Rsh8x32 x y) => (SRA (SignExt16to32 x) ...)

which sign-extends the int8 x from bit 15, but bits 8-15 of x are
garbage: for int8 a=127, b=1, (a+b)>>1 is computed from the register
value 0x80, which SignExt16to32 turns into +128, giving 64 instead of
-64. Likewise ARM64 once lowered (Rsh64x32 x y) with a bounds check
(CMPconst [64] y) that compares all 64 bits of the 32-bit count y.

The analyzer computes, top-down, how many low bits of each matched
variable the match and the result depend on, and reports a variable
the result reads more of. Generic ops' demands follow from their
signatures: Add8 needs 8 bits of each argument and its result's low d
bits need only d; Rsh32Ux64 needs all 32 bits of its first argument
and all 64 of its count; SignExt16to32 needs 16. Arch ops' demands come
from a table of ops whose operand width the instruction fixes
(compares, extensions, leading/trailing zero counts, shifts,
compare-and-swap, and the basic ALU ops that pass demand through);
other ops are not modeled and never cause a report. A variable the
condition inspects is not reported. The analyzer also reports a generic
op in a result that is asked for more bits than its width defines, such
as a 64-bit XOR of (ZeroExt16to32 x).`,
	Run: run,
}

// A demand is how many low bits of a value something depends on.
// noDemand means the demand is not known.
type demand int

const noDemand demand = -1

// A use records the largest demand on a variable and who made it.
type use struct {
	d    demand
	by   string // the consumer, such as "CMPconst (arg 0)"
	none bool   // some use's demand is unknown

	// nonzero > 0 means the variable is the argument of a CtzNNonZero
	// with N = nonzero, so its low N bits are not all zero.
	nonzero int
}

type checker struct {
	pass *analysis.Pass
	rule *rules.Rule
	res  *typecheck.Result // nil if type checking failed
	tr   *typecheck.Rule
	sem  map[string]*opSem // arch op semantics, by op name

	named  map[string]*rules.Value // named compound nodes of the match
	match  map[string]*use         // variable -> demand by the match
	result map[string]*use         // variable -> demand by the result

	// inMatch reports whether the walk is on the match side.
	// Unknown demands are resolved conservatively for each side:
	// demands are overestimated in the match and underestimated in
	// the result, so that imprecision hides reports rather than
	// inventing them.
	inMatch bool
	// ctzRoot reports whether the match root counts trailing zeros,
	// so that the result does too (by whatever algorithm).
	ctzRoot bool
	reports []string
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			res = nil // constants are then unknown, which only hides reports
		}
		sem := archTables[set.Arch.Name]
		for _, r := range set.Rules {
			if r.ResultCode != "" {
				continue
			}
			c := &checker{
				pass:   pass,
				rule:   r,
				res:    res,
				sem:    sem,
				named:  map[string]*rules.Value{},
				match:  map[string]*use{},
				result: map[string]*use{},
			}
			if res != nil {
				c.tr = res.Rule(r)
			}
			c.check()
		}
	}
	return nil
}

func (c *checker) check() {
	r := c.rule
	if !r.IsBlock() {
		c.ctzRoot = r.Match.Op.IsGeneric() && strings.HasPrefix(r.Match.Op.Name, "Ctz")
		if r.Match.Ellipsis {
			c.checkEllipsis()
			c.flush()
			return
		}
	}
	c.inMatch = true
	for _, m := range r.MatchValues() {
		m.Walk(func(v *rules.Value) bool {
			if !v.IsLeaf() && v.Name != "" {
				c.named[v.Name] = v
			}
			return true
		})
		c.visit(m, c.rootDemand(m), "", true)
	}
	c.inMatch = false
	if r.IsBlock() {
		for _, v := range r.ResultValues() {
			c.visit(v, noDemand, "", true)
		}
	} else {
		d := noDemand
		if r.Placement == "" {
			// The result replaces the matched value, so its consumers
			// demand what they demanded of the match.
			d = c.rootDemand(r.Match)
		}
		c.visit(r.Result, d, "", true)
	}
	c.compare()
	c.flush()
}

func (c *checker) flush() {
	sort.Strings(c.reports)
	for i, msg := range c.reports {
		if i == 0 || msg != c.reports[i-1] {
			c.pass.Report(c.rule.Pos, msg)
		}
	}
}

// rootDemand returns the demand on top-level match value m: its width,
// if it is a generic integer op of fixed width.
func (c *checker) rootDemand(m *rules.Value) demand {
	if m.IsLeaf() || !m.Op.IsGeneric() {
		return noDemand
	}
	sig, ok := opsig.Lookup(m.Op)
	if !ok || sig.Result.Kind != opsig.Int || sig.Result.Width == 0 {
		return noDemand
	}
	return demand(sig.Result.Width)
}

// checkEllipsis checks (Op ...) => (Op2 ...), which passes each argument
// of Op to the same argument of Op2.
func (c *checker) checkEllipsis() {
	m, res := c.rule.Match, c.rule.Result
	if res.IsLeaf() {
		return
	}
	n := int(m.Op.ArgLength)
	if n < 0 || int(res.Op.ArgLength) != n {
		return
	}
	root := c.rootDemand(m)
	for i := range n {
		name := fmt.Sprintf("arg%d", i)
		leaf := &rules.Value{Text: name, Name: name}
		c.inMatch = true
		c.visitArg(m, i, leaf, root)
		c.inMatch = false
		c.visitArg(res, i, leaf, root)
	}
	c.compare()
}

// compare reports variables that the result demands more of than the
// match does.
func (c *checker) compare() {
	var names []string
	for name := range c.result {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		ru, mu := c.result[name], c.match[name]
		if mu == nil || mu.none || mu.d < 0 || ru.d <= mu.d || c.condMentions(name) {
			continue
		}
		c.reports = append(c.reports, fmt.Sprintf(
			"%s reads %s of %s, but the match reads only %s (%s): bits %d-%d of %s are garbage",
			ru.by, bitsStr(ru.d), name, bitsStr(mu.d), mu.by, mu.d, ru.d-1, name))
	}
}

func bitsStr(d demand) string {
	if d == 1 {
		return "1 bit"
	}
	return fmt.Sprintf("%d bits", d)
}

// condMentions reports whether the rule's condition says anything about
// the value of variable name (other than its use count or block), in
// which case the condition may guarantee its upper bits.
func (c *checker) condMentions(name string) bool {
	if c.rule.CondExpr == nil {
		return false
	}
	found := false
	ast.Inspect(c.rule.CondExpr, func(n ast.Node) bool {
		if found {
			return false
		}
		switch n := n.(type) {
		case *ast.SelectorExpr:
			if id, ok := n.X.(*ast.Ident); ok && id.Name == name {
				switch n.Sel.Name {
				case "Uses", "Block", "Pos":
					return false
				}
			}
		case *ast.CallExpr:
			if id, ok := n.Fun.(*ast.Ident); ok {
				switch id.Name {
				case "clobber", "clobberIfDead", "mergePoint":
					return false
				}
			}
		case *ast.Ident:
			found = n.Name == name
		}
		return true
	})
	return found
}

// note records demand d on variable name, made by consumer by.
func (c *checker) note(name string, d demand, by string) *use {
	m := c.result
	if c.inMatch {
		m = c.match
	}
	u := m[name]
	if u == nil {
		u = &use{d: noDemand}
		m[name] = u
	}
	if d < 0 {
		u.none = true
	} else if d > u.d {
		u.d, u.by = d, by
	}
	return u
}

// visit propagates demand d to v. by describes v's consumer.
// top reports whether v is a top-level value.
func (c *checker) visit(v *rules.Value, d demand, by string, top bool) {
	if v.IsLeaf() {
		if !v.IsVar() {
			return
		}
		if n, ok := c.named[v.Name]; ok && !c.inMatch {
			// A named match subexpression: demand flows through
			// its definition.
			c.visitNode(n, d, by, false)
			return
		}
		c.note(v.Name, d, by)
		return
	}
	c.visitNode(v, d, by, top)
}

func (c *checker) visitNode(v *rules.Value, d demand, by string, top bool) {
	if !top && !c.inMatch && d > 0 && v.Op.IsGeneric() {
		if sig, ok := opsig.Lookup(v.Op); ok && sig.Result.Kind == opsig.Int && sig.Result.Width > 0 && int(d) > sig.Result.Width {
			c.reports = append(c.reports, fmt.Sprintf(
				"%s reads %s of %s, which defines only its low %d bits",
				by, bitsStr(d), v.Text, sig.Result.Width))
		}
	}
	for i, a := range v.Args {
		c.visitArg(v, i, a, d)
	}
}

// visitArg propagates demand d on v to its argument i, which is a.
func (c *checker) visitArg(v *rules.Value, i int, a *rules.Value, d demand) {
	by := fmt.Sprintf("%s (arg %d)", v.Op.Name, i)
	if c.countsZeros(v, i, a, by) {
		return
	}
	dd := c.argDemand(v, i, d)
	if x, k, ok := c.andConst(v); ok && x == a && dd >= 0 {
		// Bits of a outside the mask don't matter.
		dd = min(dd, demand(bits.Len64(k)))
	}
	if x, k, ok := c.orConst(v); ok && x == a && c.ctzRoot && !c.inMatch && dd >= 0 {
		// The result counts the trailing zeros of x|k, wherever
		// it ors in k, so bits of x above k's lowest set bit don't
		// matter (e.g. ARM's CLZ((y&-y)-1) with y = x|0x10000).
		dd = min(dd, demand(bits.TrailingZeros64(k)))
	}
	c.visit(a, dd, by, false)
}

// countsZeros handles argument i of v, which is a, if v counts trailing
// or leading zeros, and reports whether it did.
func (c *checker) countsZeros(v *rules.Value, i int, a *rules.Value, by string) bool {
	if v.Op.IsGeneric() {
		sig, ok := opsig.Lookup(v.Op)
		if !ok || i >= len(sig.Args) || sig.Args[i].Width == 0 {
			return false
		}
		w := demand(sig.Args[i].Width)
		switch genericClass(v.Op.Name, i) {
		case classCtz:
			c.ctzArg(a, w, by)
			return true
		case classCtzNonZero:
			if c.inMatch && a.IsVar() {
				c.note(a.Name, w, by).nonzero = int(w)
				return true
			}
			c.ctzArg(a, w, by)
			return true
		}
		return false
	}
	s := c.sem[v.Op.Name]
	if s == nil || i >= len(s.args) {
		return false
	}
	w := demand(s.args[0].w)
	switch s.kind {
	case kindCtz:
		c.ctzArg(a, w, by)
		return true
	case kindClz:
		if !a.IsLeaf() {
			if as := c.sem[a.Op.Name]; as != nil && as.kind == kindRev && len(a.Args) == 1 && as.args[0].w == int(w) {
				// CLZ(RBIT(x)) counts x's trailing zeros.
				c.ctzArg(a.Args[0], w, by+" of "+a.Op.Name)
				return true
			}
		}
	}
	return false
}

// ctzArg propagates the demand of a count-trailing-zeros op of width w on
// its argument a. If a is x|k for a constant k, only the bits of x below
// k's lowest set bit matter.
func (c *checker) ctzArg(a *rules.Value, w demand, by string) {
	if x, k, ok := c.orConst(a); ok {
		c.visit(x, min(w, demand(bits.TrailingZeros64(k))), by, false)
		return
	}
	if u := c.match[a.Name]; a.IsVar() && !c.inMatch && u != nil && u.nonzero > 0 && demand(u.nonzero) <= w {
		// CtzNNonZero x: x's low N bits are not all zero, so a wider
		// count of x's trailing zeros is the same.
		c.visit(a, demand(u.nonzero), by, false)
		return
	}
	c.visit(a, w, by, false)
}

// argDemand returns the demand on argument i of v, given demand d on v.
func (c *checker) argDemand(v *rules.Value, i int, d demand) demand {
	if !v.Op.IsGeneric() {
		s := c.sem[v.Op.Name]
		if s == nil || i >= len(s.args) {
			return noDemand
		}
		return c.archArgDemand(v, s.args[i], d)
	}
	sig, ok := opsig.Lookup(v.Op)
	if !ok || sig.Variadic != nil || i >= len(sig.Args) {
		return noDemand
	}
	arg := sig.Args[i]
	if arg.Kind != opsig.Int || arg.Width == 0 {
		return noDemand
	}
	w := demand(arg.Width)
	switch genericClass(v.Op.Name, i) {
	case classLow:
		// The low d bits of the result depend only on the low d bits
		// of the argument.
		if d < 0 {
			return noDemand
		}
		return min(d, w, demand(sig.Result.Width))
	case classExt:
		return c.unknown(d, w)
	case classInt64MakeHi:
		if d < 0 {
			return c.unknown(d, w)
		}
		return max(0, d-32)
	}
	return w
}

// unknown returns min(d, w), or, if d is unknown, w in the match and
// unknown in the result.
func (c *checker) unknown(d, w demand) demand {
	if d >= 0 {
		return min(d, w)
	}
	if c.inMatch {
		return w
	}
	return noDemand
}

func (c *checker) archArgDemand(v *rules.Value, a argSem, d demand) demand {
	w := demand(a.w)
	switch a.kind {
	case argFixed:
		return w
	case argLow:
		if d < 0 {
			return noDemand
		}
		return min(d, w)
	case argExt:
		return c.unknown(d, w)
	case argShl, argShr:
		// A shift by k (the auxint, or a constant second argument):
		// the low d bits of x<<k depend on the low d-k bits of x, and
		// those of x>>k on the low d+k. An unknown k is in [0, w).
		lo, hi := demand(0), w-1
		if k, ok := c.shiftCount(v); ok && k >= 0 && k < int64(w) {
			lo, hi = demand(k), demand(k)
		} else if len(v.Args) == 2 {
			// A variable count: the result depends on bits that
			// some count reaches.
			lo = 0
			if a.kind == argShr {
				lo = w
			}
		}
		if d < 0 {
			if a.kind == argShl {
				return noDemand
			}
			return c.unknown(d, w)
		}
		if a.kind == argShl {
			if c.inMatch {
				return max(0, min(d, w)-lo)
			}
			return max(0, min(d, w)-hi)
		}
		if c.inMatch {
			return min(w, d+hi)
		}
		return min(w, d+lo)
	}
	return noDemand
}

// shiftCount returns the constant count of shift v: its auxint, or its
// second argument.
func (c *checker) shiftCount(v *rules.Value) (int64, bool) {
	if len(v.Args) == 2 {
		return c.constValue(v.Args[1])
	}
	return c.constAux(v)
}

// orConst reports whether a is x|k for a constant k, returning x and k.
func (c *checker) orConst(a *rules.Value) (*rules.Value, uint64, bool) {
	return c.binConst(a, "Or", kindOr, kindOrAux)
}

// andConst reports whether a is x&k with k bounded, returning x and the
// largest value k might have, truncated to a's width.
func (c *checker) andConst(a *rules.Value) (*rules.Value, uint64, bool) {
	return c.binConst(a, "And", kindAnd, kindAndAux)
}

// binConst reports whether a is (x op k) for a constant k, where op is the
// generic op family prefix or one of the arch op kinds reg and aux.
func (c *checker) binConst(a *rules.Value, prefix string, reg, aux opKind) (*rules.Value, uint64, bool) {
	if a.IsLeaf() {
		return nil, 0, false
	}
	var w int
	if a.Op.IsGeneric() {
		rest, ok := strings.CutPrefix(a.Op.Name, prefix)
		if !ok || !isWidth(rest) || len(a.Args) != 2 {
			return nil, 0, false
		}
		w = widthOf(rest)
	} else {
		s := c.sem[a.Op.Name]
		if s == nil || len(s.args) == 0 || len(a.Args) == 0 {
			return nil, 0, false
		}
		w = s.args[0].w
		switch {
		case s.kind == aux && len(a.Args) == 1:
			if k, ok := c.constAux(a); ok {
				return a.Args[0], truncate(uint64(k), w), true
			}
			if aux != kindAndAux {
				return nil, 0, false
			}
			n := s.immBits
			if b, ok := c.auxBits(a); ok && (n == 0 || b < n) {
				n = b
			}
			if n == 0 {
				return nil, 0, false
			}
			return a.Args[0], truncate(1<<n-1, w), true
		case s.kind == kindBitSetAux && reg == kindOr && len(a.Args) == 1:
			if k, ok := c.constAux(a); ok && k >= 0 && k < int64(w) {
				return a.Args[0], 1 << k, true
			}
			return nil, 0, false
		case s.kind != reg:
			return nil, 0, false
		}
	}
	if len(a.Args) != 2 {
		return nil, 0, false
	}
	for i, k := range a.Args {
		if v, ok := c.constValue(k); ok {
			return a.Args[1-i], truncate(uint64(v), w), true
		}
	}
	return nil, 0, false
}

func truncate(k uint64, w int) uint64 {
	if w >= 64 {
		return k
	}
	return k & (1<<w - 1)
}

func widthOf(s string) int {
	switch s {
	case "8":
		return 8
	case "16":
		return 16
	case "32":
		return 32
	}
	return 64
}

// constValue returns the value of a constant op node (ConstN, MOVDconst, ...).
func (c *checker) constValue(v *rules.Value) (int64, bool) {
	if v.IsLeaf() || len(v.Args) != 0 {
		return 0, false
	}
	if v.Op.IsGeneric() {
		rest, ok := strings.CutPrefix(v.Op.Name, "Const")
		if !ok || !isWidth(rest) {
			return 0, false
		}
	} else if s := c.sem[v.Op.Name]; s == nil || s.kind != kindConst {
		return 0, false
	}
	return c.constAux(v)
}

// auxExpr returns the expression of v's auxint and its type information.
func (c *checker) auxExpr(v *rules.Value) (ast.Expr, bool) {
	if c.tr == nil || v.AuxInt == "" {
		return nil, false
	}
	e := c.tr.Expr(v, typecheck.AuxInt)
	return e, e != nil
}

// constAux returns the constant value of v's auxint, if it has one.
func (c *checker) constAux(v *rules.Value) (int64, bool) {
	e, ok := c.auxExpr(v)
	if !ok {
		return 0, false
	}
	tv, ok := c.res.Info.Types[e]
	if !ok || tv.Value == nil {
		return 0, false
	}
	return constant.Int64Val(constant.ToInt(tv.Value))
}

// auxBits returns n such that v's auxint is in [0, 1<<n), if the types in
// its expression show that, as for int32(uint8(m)).
func (c *checker) auxBits(v *rules.Value) (int, bool) {
	e, ok := c.auxExpr(v)
	if !ok {
		return 0, false
	}
	return c.nonnegBits(e)
}

func (c *checker) nonnegBits(e ast.Expr) (int, bool) {
	e = ast.Unparen(e)
	tv, ok := c.res.Info.Types[e]
	if !ok {
		return 0, false
	}
	if tv.Value != nil {
		x, ok := constant.Int64Val(constant.ToInt(tv.Value))
		if !ok || x < 0 {
			return 0, false
		}
		return bits.Len64(uint64(x)), true
	}
	n, unsigned := intBits(tv.Type)
	if call, ok := e.(*ast.CallExpr); ok && len(call.Args) == 1 {
		if ftv, ok := c.res.Info.Types[call.Fun]; ok && ftv.IsType() {
			// A conversion T(x).
			if xn, ok := c.nonnegBits(call.Args[0]); ok && (n == 0 || xn < n) {
				return xn, true
			}
		}
	}
	if unsigned {
		return n, true
	}
	return 0, false
}

// intBits returns the size in bits of integer type t and whether it is
// unsigned, or 0 if t is not a sized integer type.
func intBits(t types.Type) (int, bool) {
	b, ok := t.Underlying().(*types.Basic)
	if !ok {
		return 0, false
	}
	switch b.Kind() {
	case types.Int8:
		return 8, false
	case types.Int16:
		return 16, false
	case types.Int32:
		return 32, false
	case types.Int64:
		return 64, false
	case types.Uint8:
		return 8, true
	case types.Uint16:
		return 16, true
	case types.Uint32:
		return 32, true
	case types.Uint64:
		return 64, true
	}
	return 0, false
}

type genClass int

const (
	classFixed       genClass = iota // depends on all of the argument's bits
	classLow                         // the result's low bits depend on the argument's low bits
	classExt                         // an extension of the argument
	classCtz                         // count trailing zeros
	classCtzNonZero                  // count trailing zeros of a nonzero value
	classInt64MakeHi                 // the high word of Int64Make
)

func genericClass(name string, i int) genClass {
	for _, p := range []string{"Add", "Sub", "Mul", "And", "Or", "Xor", "Neg", "Com"} {
		if rest, ok := strings.CutPrefix(name, p); ok && isWidth(rest) {
			return classLow
		}
	}
	switch {
	case strings.HasPrefix(name, "Lsh") && i == 0,
		strings.HasPrefix(name, "Trunc"),
		name == "Int64Lo",
		name == "Int64Make" && i == 1:
		return classLow
	case name == "Int64Make":
		return classInt64MakeHi
	case strings.HasPrefix(name, "SignExt"), strings.HasPrefix(name, "ZeroExt"):
		return classExt
	case strings.HasPrefix(name, "Ctz") && strings.HasSuffix(name, "NonZero"):
		return classCtzNonZero
	case strings.HasPrefix(name, "Ctz") && isWidth(name[3:]):
		return classCtz
	}
	return classFixed
}

func isWidth(s string) bool {
	switch s {
	case "8", "16", "32", "64":
		return true
	}
	return false
}
