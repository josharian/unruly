// Package condsem checks the meaning of rules about flags and condition
// codes by evaluating them.
package condsem

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"math"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "condsem",
	Doc: `report flags and condition-code rules whose result computes something other than their match

condsem evaluates both sides of every rule that produces, consumes, or
transforms flags, over many concrete inputs (boundary integers, NaNs, and
the flags of real compares), using a model of each architecture's flags,
condition codes, and compare and select instructions. A rule is reported
if, for some input that satisfies its condition, the match and the result
compute different values, branch to different successors, or produce flags
that some condition reads differently.

For example, on ARM64

	(LTnoov (InvertFlags cmp) yes no) => (GTnoov cmp yes no)

is reported: LTnoov tests only the sign of the difference, and when cmp is
(CMP -1<<63 1) the difference overflows, so the inverted comparison's sign
is not the original's. Likewise (TESTQ x y) => (TESTL x y) is reported even
when the upper halves are zero, because the sign flag comes from bit 63 in
one and bit 31 in the other.

The models cover AMD64, 386, ARM64, ARM, PPC64, and S390X. The conditions
that codegen implements for each block kind and condition op are read from
the arch's ssa.go (blockJump, condBits); x86 SETcc and CMOVcc conditions
come from the ops' asm. Conditions are evaluated with the rule's own helpers
(FlagConstant methods, ccARM64Eval, ValAndOff, ...); conditions about use
counts, types, and placement are assumed to hold. Rules using ops or
helpers outside the model are skipped. Counterexamples avoid auxints that
earlier rules handle first; a rule wrong only for those is reported as
latent.`,
	Run: run,
}

// budget bounds the number of assignments tried per rule.
const budget = 30000

var debug = os.Getenv("UNRULY_CONDSEM_DEBUG") != ""

func run(pass *analysis.Pass) error {
	archs := make(map[string]*arch)
	skips := make(map[string]int)
	checked := 0
	reported := make(map[rules.Pos]bool)
	for _, set := range pass.Sets {
		if set.Arch.Generic {
			continue
		}
		a := archs[set.Arch.Name]
		if a == nil {
			a = newArch(set)
			if a == nil {
				continue
			}
			archs[set.Arch.Name] = a
		}
		a.findInverted(set)
		var res *typecheck.Result
		for _, r := range set.Rules {
			if !touchesFlags(a, r) {
				continue
			}
			if res == nil {
				var err error
				res, err = typecheck.Check(set)
				if err != nil {
					return err
				}
			}
			msg, skip := checkRule(a, set, r, res)
			if skip != "" {
				skips[skip]++
				if debug {
					fmt.Fprintf(os.Stderr, "condsem: skip %s: %s: %s\n", r.Pos, r.Text, skip)
				}
				continue
			}
			checked++
			if msg != "" && !reported[r.Pos] {
				reported[r.Pos] = true
				pass.Reportf(r.Pos, "%s", msg)
			}
		}
	}
	if debug {
		var ks []string
		for k := range skips {
			ks = append(ks, k)
		}
		sort.Slice(ks, func(i, j int) bool { return skips[ks[i]] > skips[ks[j]] })
		for _, k := range ks {
			fmt.Fprintf(os.Stderr, "condsem: %5d skipped: %s\n", skips[k], k)
		}
		fmt.Fprintf(os.Stderr, "condsem: %d rules checked\n", checked)
	}
	return nil
}

func newArch(set *rules.RuleSet) *arch {
	switch set.Arch.Name {
	case "AMD64", "386":
		return newX86(set.Arch)
	case "ARM64", "ARM":
		return newARM(set.Arch)
	case "PPC64":
		return newPPC64(set.Arch)
	case "S390X":
		return newS390X(set.Arch)
	}
	return nil
}

// touchesFlags reports whether r involves flags: arch blocks, or ops
// that produce or consume flags.
func touchesFlags(a *arch, r *rules.Rule) bool {
	if r.IsBlock() {
		return !r.MatchBlock.Info.IsGeneric() || !r.ResultBlock.Info.IsGeneric()
	}
	found := false
	for _, v := range append(r.MatchValues(), r.ResultValues()...) {
		v.Walk(func(v *rules.Value) bool {
			if v.Op == nil || found {
				return false
			}
			if strings.Contains(v.Op.Typ, "Flags") {
				found = true
			}
			if s := a.ops[v.Op.Name]; s != nil && !v.Op.IsGeneric() {
				if s.origin == oConst || v.Op.Name == "InvertFlags" {
					found = true
				}
				for _, w := range s.args {
					if w.k == kFlags {
						found = true
					}
				}
			}
			return true
		})
	}
	return found
}

// mismatch is panicked when the result reads flags the match didn't.
type mismatch struct{ msg string }

func (c *ctx) staleRead(cd *cond, f *flags) {
	if c.onResult {
		panic(mismatch{fmt.Sprintf("the result tests %s of flags %s, which reads a flag %s leaves unchanged", cd.name, f, f.op)})
	}
}

// checkRule evaluates r over many assignments. It returns a description
// of a difference between match and result, or a reason r can't be
// checked.
func checkRule(a *arch, set *rules.RuleSet, r *rules.Rule, res *typecheck.Result) (msg, skip string) {
	if r.ResultCode != "" {
		return "", "{code} result"
	}
	tr := res.Rule(r)
	if tr == nil {
		return "", "no type information"
	}
	if len(tr.Errors) > 0 {
		return "", "type errors"
	}
	c := &ctx{a: a, r: r, tr: tr, info: res.Info, promote: map[string]want{}, alias: map[string]string{}}
	c.lits = literals(c)
	if tr.Cond != nil {
		for _, e := range conjuncts(tr.Cond) {
			c.addAlias(e)
		}
	}
	c.matchName, c.resultName = sideNames(r)
	if r.IsBlock() {
		c.matchName = a.describeBlock(c.matchName)
		c.resultName = a.describeBlock(c.resultName)
	}
	c.leafNote = leafNote(r)
	// Prefer a counterexample that earlier rules don't handle.
	shadow, lines := shadowedAux(set, r)
	c.shadowed = shadow
	msg, skip = c.search()
	if msg != "" || len(shadow) == 0 {
		if len(shadow) > 0 {
			msg += fmt.Sprintf(" (earlier rules, %s, handle %s = %s)", lines, r.Match.AuxInt, auxList(shadow))
		}
		return msg, skip
	}
	c.shadowed = nil
	msg, skip = c.search()
	if msg != "" {
		msg += fmt.Sprintf("; the difference shows only for %s = %s, which earlier rules (%s) handle first, so this rule is wrong but latent", r.Match.AuxInt, auxList(shadow), lines)
	}
	return msg, skip
}

// search evaluates the rule over many assignments.
func (c *ctx) search() (msg, skip string) {
	c.limit = math.MaxInt
	c.en = &enumerator{}
	evals := 0
	for probe := true; ; {
		out := c.once()
		switch out.kind {
		case outSkipRule:
			return "", out.msg
		case outMismatch:
			return out.msg, ""
		case outRestart:
			c.en = &enumerator{}
			continue
		case outOK:
			evals++
		}
		if probe {
			// Size the domains so the number of paths stays within budget.
			probe = false
			if n := len(c.en.choices); n > 0 {
				c.limit = max(3, int(math.Pow(budget, 1/float64(n))))
			}
			c.en = &enumerator{}
			continue
		}
		if !c.en.next() {
			break
		}
	}
	if evals == 0 {
		return "", "no assignment satisfies the rule"
	}
	return "", ""
}

// sideNames names the root ops or block kinds of r's match and result,
// for messages: "ISEL [5]". A leaf result has no name.
func sideNames(r *rules.Rule) (string, string) {
	if r.IsBlock() {
		return r.MatchBlock.Kind, r.ResultBlock.Kind
	}
	name := func(v *rules.Value) string {
		if v.AuxInt != "" && !rules.IsVarText(v.AuxInt) && v.AuxInt != "_" {
			return v.OpName + " [" + v.AuxInt + "]"
		}
		return v.OpName
	}
	if r.Result == nil || r.Result.IsLeaf() {
		return name(r.Match), ""
	}
	return name(r.Match), name(r.Result)
}

// describeBlock adds to a block kind the condition codegen branches on,
// if that is not the kind's name: "LTnoov, which branches on MI".
func (a *arch) describeBlock(kind string) string {
	if b := a.blocks[kind]; b != nil && b.test != "" && b.test != kind {
		return kind + ", which branches on " + b.test
	}
	return kind
}

// leafNote describes a leaf result that is an arg of the match's root,
// for messages: " (ISEL's arg 1)".
func leafNote(r *rules.Rule) string {
	if r.IsBlock() || r.Result == nil || !r.Result.IsVar() {
		return ""
	}
	for i, a := range r.Match.Args {
		if a.Name == r.Result.Name {
			return fmt.Sprintf(" (%s's arg %d)", r.Match.OpName, i)
		}
	}
	return ""
}

// shadowedAux returns the auxints that earlier, unconditional rules
// handle when r's root auxint is a variable and the earlier rules' matches
// differ from r's only in having a constant there: PPC64's
// (SETBC [0] (InvertFlags bool)) shadows (SETBC [n] (InvertFlags bool))
// for n = 0. It also returns the earlier rules' lines.
func shadowedAux(set *rules.RuleSet, r *rules.Rule) (map[int64]bool, string) {
	if r.IsBlock() || r.Match.Op == nil || !rules.IsVarText(r.Match.AuxInt) {
		return nil, ""
	}
	n := r.Match.AuxInt
	shadow := map[int64]bool{}
	var lines []string
	for _, r2 := range set.ByOp[r.Match.Op] {
		if r2 == r {
			break
		}
		k, err := strconv.ParseInt(r2.Match.AuxInt, 0, 64)
		if err != nil || r2.Cond != "" {
			continue
		}
		lit := "[" + r2.Match.AuxInt + "]"
		if strings.Replace(r2.MatchText, lit, "["+n+"]", 1) != r.MatchText {
			continue
		}
		if !shadow[k] {
			shadow[k] = true
			lines = append(lines, fmt.Sprint(r2.Pos.Line))
		}
	}
	if len(shadow) == 0 {
		return nil, ""
	}
	return shadow, fmt.Sprintf("%s:%s", filepath.Base(r.Pos.File), strings.Join(lines, ","))
}

func auxList(m map[int64]bool) string {
	var ks []int64
	for k := range m {
		ks = append(ks, k)
	}
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
	var s []string
	for _, k := range ks {
		s = append(s, fmt.Sprint(k))
	}
	return strings.Join(s, ", ")
}

type outcome uint8

const (
	outOK outcome = iota
	outSkipState
	outSkipRule
	outMismatch
	outRestart
)

type result struct {
	kind outcome
	msg  string
}

// once evaluates the rule under the enumerator's next assignment.
func (c *ctx) once() (out result) {
	if c.env == nil {
		c.env = map[string]val{}
		c.genv = map[string]gv{}
		c.mem = map[string]uint64{}
	}
	clear(c.env)
	clear(c.genv)
	clear(c.mem)
	c.order = c.order[:0]
	c.onResult = false
	c.root = nil
	c.en.pos = 0
	defer func() {
		switch p := recover().(type) {
		case nil:
		case skipRule:
			out = result{kind: outSkipRule, msg: p.reason}
		case skipState:
			out = result{kind: outSkipState}
		case restart:
			out = result{kind: outRestart}
		case mismatch:
			out = result{kind: outMismatch, msg: c.describe(p.msg)}
		default:
			panic(p)
		}
	}()
	r := c.r
	var m val
	if r.IsBlock() {
		m = val{k: kSucc, s: c.block(r.MatchBlock, true)}
	} else {
		m = c.match(r.Match, wAny)
	}
	if r.Cond != "" {
		g := c.goExpr(c.tr.Cond)
		if g.k == gBool && !g.b {
			return result{kind: outSkipState}
		}
		if g.k != gBool && g.k != gTop {
			return result{kind: outSkipRule, msg: "condition is not boolean"}
		}
	}
	c.onResult = true
	var rv val
	if r.IsBlock() {
		rv = val{k: kSucc, s: c.block(r.ResultBlock, false)}
	} else {
		rv = c.result(r.Result, wAny)
	}
	if ok, d := c.compare(m, rv); !ok {
		return result{kind: outMismatch, msg: c.describe(d)}
	}
	return result{kind: outOK}
}

func (c *ctx) describe(d string) string {
	b := c.bindings()
	if b == "" {
		return d
	}
	return "for " + b + ": " + d
}

// addAlias records a condition x == y between two values: whichever is
// bound second takes the other's value rather than being enumerated.
func (c *ctx) addAlias(e ast.Expr) {
	b, ok := e.(*ast.BinaryExpr)
	if !ok || b.Op != token.EQL {
		return
	}
	x, ok1 := b.X.(*ast.Ident)
	y, ok2 := b.Y.(*ast.Ident)
	if !ok1 || !ok2 || !c.isValueVar(x.Name) || !c.isValueVar(y.Name) {
		return
	}
	c.alias[x.Name] = y.Name
	c.alias[y.Name] = x.Name
}

// isValueVar reports whether name is a match variable holding an
// *ssa.Value.
func (c *ctx) isValueVar(name string) bool {
	v := c.tr.Vars[name]
	if v == nil {
		return false
	}
	p, ok := v.Type().(*types.Pointer)
	if !ok {
		return false
	}
	n, ok := p.Elem().(*types.Named)
	return ok && n.Obj().Name() == "Value"
}

// literals returns the integer constants of the rule's match and
// condition, which are likely boundaries.
func literals(c *ctx) []uint64 {
	var lits []uint64
	seen := map[uint64]bool{}
	add := func(e ast.Expr) {
		if e == nil {
			return
		}
		ast.Inspect(e, func(n ast.Node) bool {
			x, ok := n.(ast.Expr)
			if !ok {
				return true
			}
			tv := c.info.Types[x]
			if tv.Value == nil || tv.Value.Kind() != constant.Int {
				return true
			}
			if i, ok := constant.Int64Val(tv.Value); ok && !seen[uint64(i)] {
				seen[uint64(i)] = true
				lits = append(lits, uint64(i))
			}
			return false
		})
	}
	for _, v := range c.r.MatchValues() {
		v.Walk(func(v *rules.Value) bool {
			if v.AuxInt != "" && !rules.IsVarText(v.AuxInt) {
				add(c.tr.Expr(v, typecheck.AuxInt))
			}
			return true
		})
	}
	add(c.tr.Cond)
	sort.Slice(lits, func(i, j int) bool { return lits[i] < lits[j] })
	return lits
}
