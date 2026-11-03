// Package difftest checks generic rewrite rules by random testing.
package difftest

import (
	"errors"
	"fmt"
	"hash/fnv"
	"math/rand/v2"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/internal/gensem"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "difftest",
	Doc: `report generic rules whose result differs from their match on some input

difftest runs each rule whose match and result use only generic ops on
random inputs. It builds a value tree with the shape of the match,
matches the rule against it exactly as rulegen's generated code would
(commutative orders, repeated variables, the condition, with the
compiler's own helpers), skips trees that an earlier rule for the same
op would rewrite instead, builds the result, and compares the values of
match and result bit for bit. For example, in

	(Lsh64x64 (And64 (Rsh64x64 <t> x (Const64 <t2> [c])) (Const64 [d])) (Const64 [e])) && c < e
		=> (And64 (Lsh64x64 <t> x (Const64 <t2> [e-c])) (Const64 <t> [d<<e]))

the shift counts are unsigned, but c < e compares them as int64s. With
c = -1 (a shift by 1<<64-1, which shifts in copies of the sign bit),
d = 1, e = 1, and x = -1, the match ((x>>c)&1)<<1 is 2, but the result
(x<<2)&2 is 0. difftest reports that input.

It also reports results that crash the compiler (a Go panic in a
condition or aux expression), that use an op outside its domain (such as
a shift marked bounded by an amount that is not), or that build a float
constant holding a NaN.

A counterexample is "latent" if rewriting its sub-values first, with the
other rules of the same rule set, makes it go away (for example, because
an inner shift by 64 folds to 0 and the outer rule no longer matches);
the bug then shows only if the rewrite pass visits the outer value first.
If the rewritten input still exposes the bug, difftest reports that input
instead. Generated inputs are well-typed
generic SSA and respect each op's documented preconditions (bounded
shifts, Avg64u's arg0 >= arg1, an unsigned division of a signed type has
non-negative args, ...). Rules whose expressions the model cannot
evaluate are skipped.`,
	Run: run,
}

const (
	maxTries = 3000
	wantSat  = 400
)

func run(pass *analysis.Pass) error {
	t := &tester{pass: pass, matchers: map[*gensem.Config]*gensem.Matcher{}}
	for _, set := range pass.Sets {
		for _, c := range gensem.ArchConfigs(set.Arch.Name) {
			if t.matchers[c] == nil {
				t.matchers[c] = gensem.NewMatcher(c)
			}
		}
	}
	// Report the most severe finding among a rule's | expansions.
	best := map[rules.Pos]*finding{}
	var order []rules.Pos
	for r := range pass.Rules() {
		if r.IsBlock() || !genericOnly(r) {
			continue
		}
		f := t.check(r)
		if f == nil {
			continue
		}
		if old := best[r.Pos]; old == nil {
			order = append(order, r.Pos)
			best[r.Pos] = f
		} else if f.rank() < old.rank() {
			best[r.Pos] = f
		}
	}
	for _, pos := range order {
		pass.Report(pos, best[pos].msg)
	}
	return nil
}

// genericOnly reports whether r's match and result use only generic ops
// that opsig describes (and so the interpreter may model).
func genericOnly(r *rules.Rule) bool {
	ok := true
	check := func(v *rules.Value) bool {
		if v.Op != nil {
			if !v.Op.IsGeneric() || v.Op.SIMD {
				ok = false
			} else if _, known := opsig.Lookup(v.Op); !known {
				ok = false
			}
		}
		return ok
	}
	r.Match.Walk(check)
	if r.Result != nil {
		r.Result.Walk(check)
	}
	return ok
}

// trace, if set, is told the outcome of testing each rule: how many
// generated inputs satisfied it, and why testing stopped early, if it did.
var trace func(r *rules.Rule, sat int, stop error)

type tester struct {
	pass     *analysis.Pass
	matchers map[*gensem.Config]*gensem.Matcher
}

type finding struct {
	kind   kind
	normal bool
	msg    string
}

type kind int

const (
	miscompile kind = iota
	crash
	hostDependent
	invalid
)

func (f *finding) rank() int {
	r := int(f.kind)
	if !f.normal {
		r += 10
	}
	return r
}

func seed(r *rules.Rule) uint64 {
	h := fnv.New64a()
	h.Write([]byte(r.Text))
	return h.Sum64()
}

// check tests r and returns its most severe finding, or nil.
func (t *tester) check(r *rules.Rule) *finding {
	f, sat, stop := t.check1(r)
	if trace != nil {
		trace(r, sat, stop)
	}
	return f
}

func (t *tester) check1(r *rules.Rule) (*finding, int, error) {
	rng := rand.New(rand.NewPCG(seed(r), 1))
	gen := &gensem.Gen{Rand: rng, Generic: t.pass.Ops.Generic, Pool: gensem.RulePool(r)}
	var best *finding
	genFails, sat := 0, 0
	configs := gensem.ArchConfigs(r.Set.Arch.Name)
	for try := 0; try < maxTries && sat < wantSat; try++ {
		cfg := configs[try%len(configs)]
		gen.Matcher = t.matchers[cfg]
		lhs, err := gen.Generate(r)
		if err != nil {
			if genFails++; genFails > 50 && sat == 0 {
				return best, sat, err
			}
			continue
		}
		tr := &trial{t: t, r: r, cfg: cfg, garbage: rng.Uint64()}
		f, matched, err := tr.eval(lhs)
		if err != nil {
			return best, sat, err
		}
		if matched {
			sat++
		}
		if f == nil || best != nil && best.rank() <= f.rank() {
			continue
		}
		best = tr.shrink(lhs, f, func() { gen.Solve(r, lhs) })
	}
	return best, sat, nil
}

// A trial runs one rule on generated inputs for one target.
type trial struct {
	t       *tester
	r       *rules.Rule
	cfg     *gensem.Config
	garbage uint64
}

// eval runs the trial's rule on lhs, as run does, and classifies any
// finding as normal or latent.
func (tr *trial) eval(lhs *gensem.Value) (f *finding, matched bool, err error) {
	f, matched, err = tr.run(lhs)
	if f == nil || err != nil {
		return f, matched, err
	}
	return tr.settle(lhs, f), matched, nil
}

// settle decides whether the finding f for lhs survives rewriting the
// proper sub-values of lhs first, with the rules of the same set. If it
// does, settle returns the finding for the rewritten input, marked
// normal. Otherwise it returns f, marked latent.
func (tr *trial) settle(lhs *gensem.Value, f *finding) *finding {
	m := tr.t.matchers[tr.cfg]
	sub, by := rewritable(m, tr.r.Set, lhs)
	if sub == nil {
		f.normal = true
		return f
	}
	n := &normalizer{m: m, set: tr.r.Set, done: map[*gensem.Value]*gensem.Value{}, budget: 100}
	if nl, err := n.args(lhs); err == nil {
		if nf, _, err := tr.run(nl); err == nil && nf != nil {
			nf.normal = true
			return nf
		}
	}
	in := gensem.NewInterp(m.Cfg, genericOps)
	f.normal = false
	f.msg = fmt.Sprintf("latent: %s [needs %s, which %s rewrites, to be visited later]", f.msg, in.Format(sub), by)
	return f
}

// run runs the trial's rule on lhs. It returns the finding, if any, and
// whether the rule matched. An error means the rule can't be evaluated.
func (tr *trial) run(lhs *gensem.Value) (f *finding, matched bool, err error) {
	r, cfg := tr.r, tr.cfg
	m := tr.t.matchers[cfg]
	in := gensem.NewInterp(cfg, genericOps)
	in.Garbage = tr.garbage
	reject := func(why string) {
		if traceReject != nil {
			traceReject(why, in.Format(lhs))
		}
	}
	report := func(k kind, format string, args ...any) {
		f = &finding{kind: k, msg: fmt.Sprintf(format, args...) + " (" + cfg.Arch + ")"}
	}

	// The value of the match. If it is machine-dependent (lvalOK is
	// false), the rule must still not crash or depend on the host.
	lval, err := in.Eval(lhs)
	lvalOK := err == nil
	var unspec *gensem.Unspecified
	switch {
	case err == nil:
	case isUnsupported(err):
		return nil, false, err
	case errors.As(err, &unspec):
	default:
		reject("invalid: " + err.Error())
		return nil, false, nil // not a valid input
	}
	if shadowed(m, earlierRules(r), lhs) {
		reject("shadowed")
		return nil, false, nil
	}
	env, ok, err := m.Match(r, lhs)
	if err != nil {
		if isUnsupported(err) {
			return nil, false, err
		}
		report(kindOf(err), "condition fails with %v on %s", err, in.Format(lhs))
		return f, false, nil
	}
	if !ok {
		reject("no match")
		return nil, false, nil
	}
	res, err := m.Build(r, env)
	if err != nil {
		if isUnsupported(err) {
			return nil, true, err
		}
		report(kindOf(err), "building the result fails with %v for %s", err, in.Format(lhs))
		return f, true, nil
	}
	rval, err := in.Eval(res)
	fm := in.FormatAll(lhs, res)
	if err != nil {
		var undef *gensem.Undefined
		var ill *gensem.IllTyped
		switch {
		case isUnsupported(err):
			return nil, true, err
		case errors.As(err, &undef):
			report(invalid, "%s is rewritten to %s, which applies %s outside its domain (%s)", fm[0], fm[1], undef.Op, undef.Msg)
		case errors.As(err, &ill):
			report(invalid, "%s is rewritten to %s, which is ill-typed: %s: %s", fm[0], fm[1], ill.Op, ill.Msg)
		case errors.As(err, &unspec) && lvalOK:
			report(miscompile, "%s is %s, but its rewrite %s is machine-dependent: %v", fm[0], lval, fm[1], err)
		}
		return f, true, nil
	}
	if !lvalOK {
		return nil, true, nil
	}
	if lval.Kind == gensem.KInt && rval.Kind == gensem.KInt && rval.Width > lval.Width {
		// A wider result stands for its low bits.
		rval = gensem.IntVal(lval.Width, rval.Bits)
	}
	switch {
	case lval.Kind != rval.Kind || lval.Width != rval.Width:
		if r.Set.Arch.Generic {
			report(invalid, "%s is %s, but its rewrite %s is %s", fm[0], describe(lval), fm[1], describe(rval))
		}
		// Otherwise, lowering may change representation:
		// a bool is a byte, a float32 lives in a float64.
	case !lval.Equal(rval):
		report(miscompile, "%s is %s, but its rewrite %s is %s", fm[0], lval, fm[1], rval)
	}
	return f, true, nil
}

// shrink simplifies the counterexample lhs, which has finding f, while
// it keeps a finding of the same kind, and returns the final finding.
// It mutates lhs, calling solve after each change to restore the rule's
// equality conditions.
func (tr *trial) shrink(lhs *gensem.Value, f *finding, solve func()) *finding {
	slots := gensem.Slots(lhs)
	for range 200 {
		progress := false
		for _, s := range slots {
			for _, c := range s.Simpler() {
				saved := make([]uint64, len(slots))
				for i, s := range slots {
					saved[i] = s.Get()
				}
				s.Set(c)
				solve()
				nf, _, err := tr.eval(lhs)
				if err == nil && nf != nil && nf.kind == f.kind && (nf.normal || !f.normal) {
					f, progress = nf, true
					break
				}
				for i, s := range slots {
					s.Set(saved[i])
				}
			}
		}
		if !progress {
			break
		}
	}
	return f
}

// kindOf classifies an error from evaluating a rule's Go code.
func kindOf(err error) kind {
	var inv *gensem.Invalid
	var host *gensem.HostDependent
	switch {
	case errors.As(err, &inv):
		return invalid
	case errors.As(err, &host):
		return hostDependent
	}
	return crash
}

var genericOps = gensem.GenericOps()

func describe(v gensem.Val) string {
	switch v.Kind {
	case gensem.KInt:
		return fmt.Sprintf("a %d-bit integer", v.Width)
	case gensem.KFloat:
		return fmt.Sprintf("a float%d", v.Width)
	case gensem.KBool:
		return "a bool"
	case gensem.KTuple:
		return "a tuple"
	}
	return "a flags value"
}

func isUnsupported(err error) bool {
	var u *gensem.Unsupported
	return errors.As(err, &u)
}

// A normalizer rewrites value trees with the rules of a set, as the
// rewrite pass would if it visited every arg before its user.
type normalizer struct {
	m      *gensem.Matcher
	set    *rules.RuleSet
	done   map[*gensem.Value]*gensem.Value // value to its normal form
	budget int                             // rewrites left
}

var errUndecided = errors.New("normal form undecided")

// args returns a copy of v with each arg in normal form.
func (n *normalizer) args(v *gensem.Value) (*gensem.Value, error) {
	args := make([]*gensem.Value, len(v.Args))
	changed := false
	for i, a := range v.Args {
		na, err := n.value(a)
		if err != nil {
			return nil, err
		}
		args[i] = na
		changed = changed || na != a
	}
	if !changed {
		return v, nil
	}
	nv := *v
	nv.Args = args
	return &nv, nil
}

// value returns the normal form of v. Shared sub-values stay shared.
func (n *normalizer) value(v *gensem.Value) (*gensem.Value, error) {
	if v.Op == nil {
		return v, nil
	}
	if nv, ok := n.done[v]; ok {
		return nv, nil
	}
	cur, err := n.args(v)
	if err != nil {
		return nil, err
	}
	for _, r := range n.set.ByOp[cur.Op] {
		if r.IsBlock() {
			continue
		}
		env, ok, err := n.m.Match(r, cur)
		if err != nil {
			return nil, errUndecided
		}
		if !ok {
			continue
		}
		if n.budget--; n.budget < 0 {
			return nil, errUndecided
		}
		res, err := n.m.Build(r, env)
		if err != nil {
			return nil, errUndecided
		}
		if !r.Result.IsLeaf() {
			// The rewrite pass resets the value in place,
			// keeping its uses.
			res.Uses = v.Uses
		}
		if cur, err = n.value(res); err != nil {
			return nil, err
		}
		break
	}
	n.done[v] = cur
	n.done[cur] = cur
	return cur, nil
}

// earlierRules returns the rules for r's op that precede r in its set.
func earlierRules(r *rules.Rule) []*rules.Rule {
	var res []*rules.Rule
	for _, e := range r.Set.ByOp[r.Match.Op] {
		if e == r {
			break
		}
		res = append(res, e)
	}
	return res
}

// shadowed reports whether one of earlier might match v. If that can't be
// decided, it assumes so.
func shadowed(m *gensem.Matcher, earlier []*rules.Rule, v *gensem.Value) bool {
	for _, e := range earlier {
		if _, ok, err := m.Match(e, v); ok || err != nil {
			return true
		}
	}
	return false
}

// traceReject, if set, is told why a generated input was not used.
var traceReject func(why, lhs string)

// rewritable returns a proper sub-value of v that some rule of set might
// rewrite, and that rule's position, or nil.
func rewritable(m *gensem.Matcher, set *rules.RuleSet, v *gensem.Value) (*gensem.Value, string) {
	for _, a := range v.Args {
		if a.Op == nil {
			continue
		}
		for _, r := range set.ByOp[a.Op] {
			if r.IsBlock() {
				continue
			}
			if _, ok, err := m.Match(r, a); ok || err != nil {
				return a, shortPos(r.Pos)
			}
		}
		if s, by := rewritable(m, set, a); s != nil {
			return s, by
		}
	}
	return nil, ""
}

func shortPos(p rules.Pos) string {
	f := p.File
	if i := strings.LastIndexAny(f, `/\`); i >= 0 {
		f = f[i+1:]
	}
	return fmt.Sprintf("%s:%d", f, p.Line)
}
