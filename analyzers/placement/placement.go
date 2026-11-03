// Package placement reports rules that create values in a block where
// they are not valid.
package placement

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"slices"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "placement",
	Doc: `report rules that create values in a block where they are invalid

A rule's result values are created in the rewritten value's block (v.Block),
in the block b of a block rule, or wherever @x.Block or @mergePoint(b, ...)
says. Values bound deeper in the match may live in other blocks, so the
result must respect where they are:

  - Every argument must dominate the block it is used in.
    (Load <t1> op1:(OffPtr [o1] p1) (Store {t2} p2 _ mem:(Zero [n] p3 _))) => @mem.Block (Load <t1> op1 mem)
    uses op1, an argument of the root Load, in the Zero's block, which op1
    need not dominate.
  - A value that reads memory must be in a block where that memory state is
    current. (BSWAPQ x:(MOVQload [i] {s} p mem)) => (MOVBEQload [i] {s} p mem)
    creates a load of the MOVQload's memory state in the BSWAPQ's block; if a
    store intervenes, two memory states are live.
  - A merged load that also takes other arguments needs canMergeLoad, which
    checks that those arguments don't depend on a later memory state.
  - A tuple selector (Select0, Select1, SelectN) must be in its tuple's block,
    in generic rules (after lowering, the tighten tuple selectors pass
    moves misplaced selectors).
  - A Phi's arguments correspond to its block's predecessors, so only a rule
    rooted at a Phi of the same arity can create one.
  - @mergePoint(b, x...) must match the condition's mergePoint(b, x...),
    and a combined load placed with @x.Block must not subsume a load that
    may be in a later block (after a bounds check, say).

Block equalities come from @placement and from conditions such as
x.Block == v.Block, b == x.Block, and canMergeLoad(v, x).`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	mem := inferMem(pass.Corpus)
	for r := range pass.Rules() {
		c := newChecker(pass, mem, r)
		if c == nil {
			continue
		}
		c.check()
	}
	return nil
}

// A class is a set of blocks known to be equal, such as v.Block and
// x.Block given the condition x.Block == v.Block.
// Class 0 is the rewritten value's block, v.Block, which is b.
//
// A term is a class or the pred'th predecessor of a class's block.
type term struct {
	class int
	pred  int // -1 for the class itself
}

type checker struct {
	pass *analysis.Pass
	mem  *memInfo
	r    *rules.Rule

	uf     []int                // union-find over classes
	vars   map[string]int       // the class of each match-bound variable's definition
	nodes  map[*rules.Value]int // the class of each compound match node
	parent map[*rules.Value]*rules.Value
	edges  []edge // dominance facts
	phis   []*rules.Value

	occs     map[string][]*rules.Value // every match occurrence of each variable
	canMerge map[string]bool           // l in canMergeLoad(_, l)
	condMP   []string                  // the args of a condition's mergePoint(b, ...) != nil, if any

	place     place
	reported  map[string]bool
	isGeneric bool
}

// An edge says that the definition block of class from dominates to.
type edge struct {
	from int
	to   term
}

// A place is where a rule creates its result values.
type place struct {
	classes []int  // one class, or a mergePoint's arguments' classes
	merge   bool   // a mergePoint: the block of whichever class is last
	desc    string // such as "v.Block"
}

func newChecker(pass *analysis.Pass, mem *memInfo, r *rules.Rule) *checker {
	if r.ResultCode != "" {
		return nil
	}
	c := &checker{
		pass:      pass,
		mem:       mem,
		r:         r,
		vars:      make(map[string]int),
		nodes:     make(map[*rules.Value]int),
		parent:    make(map[*rules.Value]*rules.Value),
		occs:      make(map[string][]*rules.Value),
		canMerge:  make(map[string]bool),
		reported:  make(map[string]bool),
		isGeneric: r.Set.Arch.Generic,
	}
	root := c.newClass() // 0
	c.vars["b"] = root
	if !r.IsBlock() {
		c.vars["v"] = root
	}
	for _, v := range r.MatchValues() {
		c.bind(v, nil, 0)
	}
	c.parseCond()
	if !c.parsePlacement() {
		return nil
	}
	return c
}

func (c *checker) newClass() int {
	c.uf = append(c.uf, len(c.uf))
	return len(c.uf) - 1
}

func (c *checker) find(x int) int {
	for c.uf[x] != x {
		c.uf[x] = c.uf[c.uf[x]]
		x = c.uf[x]
	}
	return x
}

func (c *checker) union(x, y int) { c.uf[c.find(x)] = c.find(y) }

// varClass returns the class of name's definition, creating it if needed.
func (c *checker) varClass(name string) int {
	k, ok := c.vars[name]
	if !ok {
		k = c.newClass()
		c.vars[name] = k
	}
	return k
}

// bind records match node v, an argument of parent (nil for a top-level
// match value), and its descendants.
func (c *checker) bind(v, parent *rules.Value, i int) {
	c.parent[v] = parent
	var k int
	switch {
	case !v.IsLeaf():
		if parent == nil && !c.r.IsBlock() {
			k = 0
			if rules.IsVarText(v.Name) {
				c.vars[v.Name] = 0
			}
		} else if rules.IsVarText(v.Name) {
			k = c.varClass(v.Name)
		} else {
			k = c.newClass()
		}
		c.nodes[v] = k
		if v.Op.Name == "Phi" && v.Op.IsGeneric() {
			c.phis = append(c.phis, v)
		}
	case v.IsVar():
		k = c.varClass(v.Name)
	default:
		return // _
	}
	if rules.IsVarText(v.Name) {
		c.occs[v.Name] = append(c.occs[v.Name], v)
	}
	// v's definition dominates its use.
	switch {
	case parent == nil && c.r.IsBlock():
		c.edges = append(c.edges, edge{k, term{0, -1}}) // a control dominates its block
	case parent == nil:
	case isPhi(parent):
		c.edges = append(c.edges, edge{k, term{c.nodes[parent], i}})
	default:
		c.edges = append(c.edges, edge{k, term{c.nodes[parent], -1}})
	}
	for j, a := range v.Args {
		c.bind(a, v, j)
	}
}

func isPhi(v *rules.Value) bool { return v.Op != nil && v.Op.IsGeneric() && v.Op.Name == "Phi" }

// parseCond records the block equalities that r's condition implies.
func (c *checker) parseCond() {
	if c.r.CondExpr == nil {
		return
	}
	for _, e := range conjuncts(c.r.CondExpr) {
		switch e := e.(type) {
		case *ast.BinaryExpr:
			if e.Op == token.EQL {
				x, okx := c.blockOf(e.X)
				y, oky := c.blockOf(e.Y)
				if okx && oky {
					c.union(x, y)
				}
			}
			if call, ok := e.X.(*ast.CallExpr); ok && e.Op == token.NEQ && funcName(call) == "mergePoint" && len(call.Args) > 0 && isNil(e.Y) {
				c.condMP = identArgs(call.Args[1:])
			}
		case *ast.CallExpr:
			switch funcName(e) {
			case "canMergeLoad", "canMergeLoadClobber":
				// canMergeLoad(target, load) requires target.Block == load.Block.
				args := identArgs(e.Args)
				if len(args) < 2 || args[0] == "" || args[1] == "" {
					continue
				}
				c.union(c.varClass(args[0]), c.varClass(args[1]))
				c.canMerge[args[1]] = true
			}
		}
	}
}

// conjuncts splits e into its top-level && operands.
func conjuncts(e ast.Expr) []ast.Expr {
	switch x := e.(type) {
	case *ast.ParenExpr:
		return conjuncts(x.X)
	case *ast.BinaryExpr:
		if x.Op == token.LAND {
			return append(conjuncts(x.X), conjuncts(x.Y)...)
		}
	}
	return []ast.Expr{e}
}

// funcName returns the name of the function call calls, without any
// package qualifier, with its first letter lowercased: canMergeLoad for
// both canMergeLoad and ssa.CanMergeLoad.
func funcName(call *ast.CallExpr) string {
	var name string
	switch f := call.Fun.(type) {
	case *ast.Ident:
		name = f.Name
	case *ast.SelectorExpr:
		name = f.Sel.Name
	default:
		return ""
	}
	r, n := utf8.DecodeRuneInString(name)
	return string(unicode.ToLower(r)) + name[n:]
}

func isNil(e ast.Expr) bool {
	id, ok := e.(*ast.Ident)
	return ok && id.Name == "nil"
}

// identArgs returns the names of args, with "" for non-identifiers.
func identArgs(args []ast.Expr) []string {
	var names []string
	for _, a := range args {
		id, _ := a.(*ast.Ident)
		if id == nil {
			names = append(names, "")
			continue
		}
		names = append(names, id.Name)
	}
	return names
}

// blockOf returns the class of the block e denotes: b or x.Block.
func (c *checker) blockOf(e ast.Expr) (int, bool) {
	switch e := e.(type) {
	case *ast.Ident:
		if e.Name == "b" {
			return 0, true
		}
	case *ast.SelectorExpr:
		if id, ok := e.X.(*ast.Ident); ok && e.Sel.Name == "Block" {
			if k, ok := c.vars[id.Name]; ok {
				return k, true
			}
		}
	}
	return 0, false
}

// parsePlacement sets c.place. It reports false for a placement it
// doesn't understand.
func (c *checker) parsePlacement() bool {
	p := c.r.Placement
	switch {
	case p == "":
		c.place = place{classes: []int{0}, desc: "v.Block"}
		if c.r.IsBlock() {
			c.place.desc = "the " + c.r.MatchBlock.Kind + " block"
		}
		return true
	case p == "b.Func.Entry":
		c.place = place{classes: []int{c.newClass()}, desc: p}
		return true
	}
	e, err := parser.ParseExpr(p)
	if err != nil {
		return false
	}
	if k, ok := c.blockOf(e); ok {
		c.place = place{classes: []int{k}, desc: p}
		return true
	}
	call, ok := e.(*ast.CallExpr)
	if !ok || funcName(call) != "mergePoint" || len(call.Args) < 2 {
		return false
	}
	c.place = place{merge: true, desc: p}
	for _, name := range identArgs(call.Args[1:]) {
		k, ok := c.vars[name]
		if !ok {
			return false
		}
		c.place.classes = append(c.place.classes, k)
	}
	if !slices.Equal(identArgs(call.Args[1:]), c.condMP) {
		c.report("result is placed at @%s, but the condition doesn't check %s != nil", p, p)
	}
	return true
}

func (c *checker) report(format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	if !c.reported[msg] {
		c.reported[msg] = true
		c.pass.Report(c.r.Pos, msg)
	}
}

// dominated returns the terms that class k's definition block dominates.
func (c *checker) dominated(k int) map[term]bool {
	s := map[term]bool{{c.find(k), -1}: true}
	for changed := true; changed; {
		changed = false
		for _, e := range c.edges {
			to := term{c.find(e.to.class), e.to.pred}
			if s[term{c.find(e.from), -1}] && !s[to] {
				s[to] = true
				changed = true
			}
		}
		// A value that dominates every predecessor of a Phi's block
		// dominates that block.
		for _, p := range c.phis {
			if p.Rest {
				continue
			}
			pk := c.find(c.nodes[p])
			if s[term{pk, -1}] {
				continue
			}
			all := true
			for i := range p.Args {
				all = all && s[term{pk, i}]
			}
			if all {
				s[term{pk, -1}] = true
				changed = true
			}
		}
	}
	return s
}

// dominates reports whether variable x is available in place p
// (or, if pred >= 0, at the end of its pred'th predecessor).
func (c *checker) dominates(x string, p place, pred int) bool {
	s := c.dominated(c.vars[x])
	for _, k := range p.classes {
		if s[term{c.find(k), pred}] {
			// For a mergePoint, every argument's block dominates the
			// merge point, so any one suffices.
			return true
		}
	}
	return false
}

// inBlock reports whether class k is known to be each of p's blocks.
func (c *checker) inBlock(k int, p place) bool {
	for _, pk := range p.classes {
		if c.find(pk) != c.find(k) {
			return false
		}
	}
	return true
}

// current reports whether memory state m is current in each of p's
// blocks: m is defined there, or something there uses it.
//
// It also accepts an m that a matched memory op (a store, call, or
// atomic) consumes. Then m is current up to that op's memory result, and
// whether the rule may extend m past it depends on that result's other
// uses, not on placement.
func (c *checker) current(m string, p place) bool {
	for _, pk := range p.classes {
		if !c.currentIn(m, pk) {
			return false
		}
	}
	return true
}

func (c *checker) currentIn(m string, k int) bool {
	if c.find(c.vars[m]) == c.find(k) {
		return true
	}
	for _, o := range c.occs[m] {
		if p := c.parent[o]; p != nil && !isPhi(p) && (c.find(c.nodes[p]) == c.find(k) || c.mem.carriesMem(p.Op)) {
			return true
		}
		if c.parent[o] == nil && c.r.IsBlock() && c.find(k) == 0 {
			return true
		}
	}
	return false
}

func (c *checker) check() {
	r := c.r
	for _, v := range r.ResultValues() {
		if v.IsLeaf() {
			// v becomes a copy of x (or x becomes a control) in place.
			if c.bound(v) && !c.dominates(v.Name, c.place, -1) {
				c.report("result %s is used in %s, but %s %s", v.Name, c.place.desc, v.Name, c.whyNot(v.Name))
			}
			continue
		}
		c.checkCreated(v)
	}
	c.checkHoist()
}

// bound reports whether result leaf v is a variable bound by the match.
func (c *checker) bound(v *rules.Value) bool {
	if !v.IsVar() {
		return false
	}
	_, ok := c.occs[v.Name]
	return ok
}

// checkCreated checks result value v, which the rule creates in c.place,
// and its descendants.
func (c *checker) checkCreated(v *rules.Value) {
	if isPhi(v) && !c.checkPhi(v) {
		return // its args' dominance is moot
	}
	isSelector := c.isGeneric && v.Op.IsGeneric() && (v.Op.Name == "Select0" || v.Op.Name == "Select1" || v.Op.Name == "SelectN")
	for i, a := range v.Args {
		if !a.IsLeaf() {
			c.checkCreated(a)
			continue
		}
		if !c.bound(a) {
			continue
		}
		pred := -1
		if isPhi(v) {
			pred = i
		}
		if !c.dominates(a.Name, c.place, pred) {
			c.report("%s is created in %s, but its arg %s %s", v.Op, c.place.desc, a.Name, c.whyNot(a.Name))
			continue
		}
		if isSelector && !c.inBlock(c.vars[a.Name], c.place) {
			c.report("%s of %s is created in %s, but a tuple selector must be in its tuple's block, and %s need not be in %s; use @%s.Block",
				v.Op, a.Name, c.place.desc, a.Name, c.place.desc, a.Name)
		}
		if c.mem.isMemArg(v, i) {
			c.checkMem(v, a.Name)
		}
	}
}

// whyNot explains why x need not dominate c.place.
func (c *checker) whyNot(x string) string {
	for _, o := range c.occs[x] {
		for p := c.parent[o]; p != nil; p = c.parent[p] {
			if isPhi(p) {
				return fmt.Sprintf("is bound under a Phi arg, so it need not dominate %s", c.place.desc)
			}
		}
	}
	if c.r.Placement == "" {
		return fmt.Sprintf("need not dominate %s", c.place.desc)
	}
	return fmt.Sprintf("is bound outside %s and need not dominate %s", strings.TrimSuffix(c.r.Placement, ".Block"), c.place.desc)
}

// checkMem checks that v, created in c.place, may read memory state m.
func (c *checker) checkMem(v *rules.Value, m string) {
	if !c.current(m, c.place) {
		var from string
		for _, o := range c.occs[m] {
			if p := c.parent[o]; p != nil && !isPhi(p) {
				from = p.Op.String()
				if rules.IsVarText(p.Name) {
					from = p.Name + " (" + from + ")"
				}
				break
			}
		}
		fix := ""
		if from != "" && c.r.Placement == "" {
			if name, _, ok := strings.Cut(from, " "); ok {
				fix = fmt.Sprintf("; use @%s.Block or require %s.Block == v.Block", name, name)
			}
		}
		if from == "" {
			from = "the match"
		}
		if c.place.merge {
			c.report("%s is created in %s with memory arg %s from %s; the merge point is the latest of those values' blocks, where %s need not be current: if a store precedes it, two memory states are live",
				v.Op, c.place.desc, m, from, m)
			return
		}
		c.report("%s is created in %s with memory arg %s from %s, which may be in an earlier block; if a store intervenes, two memory states are live%s",
			v.Op, c.place.desc, m, from, fix)
		return
	}
	c.checkMerge(v, m)
}

// checkMerge checks a value v that reads memory state m, which some
// load L in the match also reads. If v also takes values from outside
// L, one of them might depend on a later memory state, as in
//
//	load = MOVQload ptr oldmem
//	newmem = MOVQstore ... oldmem
//	x = MOVQload ptr2 newmem
//	v = ADDQ x load
//
// Then ADDQload x ptr oldmem must follow x and precede newmem, which is
// impossible. canMergeLoad checks for this.
func (c *checker) checkMerge(v *rules.Value, m string) {
	if c.r.IsBlock() {
		return
	}
	var loads []*rules.Value
	for _, o := range c.occs[m] {
		p := c.parent[o]
		if p == nil || isPhi(p) {
			continue
		}
		if c.parent[p] == nil && !c.r.IsBlock() || c.mem.carriesMem(p.Op) {
			// The root reads m itself, or m is consumed by a
			// store, call, or atomic; see current.
			return
		}
		loads = append(loads, p)
	}
	if len(loads) == 0 {
		return
	}
	for _, l := range loads {
		if rules.IsVarText(l.Name) && c.canMerge[l.Name] {
			return
		}
	}
	inside := make(map[string]bool)
	for _, l := range loads {
		l.Walk(func(x *rules.Value) bool {
			if rules.IsVarText(x.Name) {
				inside[x.Name] = true
			}
			return true
		})
	}
	var outside []string
	var walk func(x *rules.Value)
	walk = func(x *rules.Value) {
		for _, a := range x.Args {
			if !a.IsLeaf() {
				walk(a)
			} else if c.bound(a) && !inside[a.Name] && !slices.Contains(outside, a.Name) {
				outside = append(outside, a.Name)
			}
		}
	}
	walk(v)
	if len(outside) == 0 {
		return
	}
	l := loads[0]
	name := l.Op.String()
	if rules.IsVarText(l.Name) {
		name = l.Name
	}
	c.report("%s merges the load %s but also takes %s from outside it; without canMergeLoad(v, %s), %s may depend on a later memory state, leaving no valid schedule",
		v.Op, name, strings.Join(outside, ", "), name, strings.Join(outside, ", "))
}

// checkPhi checks a Phi that the rule creates and reports whether it is
// well placed.
func (c *checker) checkPhi(v *rules.Value) bool {
	for _, p := range c.phis {
		if !p.Rest && len(p.Args) == len(v.Args) && c.inBlock(c.nodes[p], c.place) {
			return true
		}
	}
	where := "a value rule not rooted at a Phi"
	if c.r.IsBlock() {
		where = "a block rule"
	}
	c.report("Phi is created in %s by %s; a Phi's args correspond to its block's predecessors, so only a rule rooted at a %d-arg Phi may create one",
		c.place.desc, where, len(v.Args))
	return false
}

// checkHoist checks a result placed at @x.Block: if the match has
// another load outside x, which may be in a later block (after a bounds
// check, say), the result executes before it.
func (c *checker) checkHoist() {
	r := c.r
	if r.Placement == "" || c.place.merge || r.IsBlock() || r.Result == nil || r.Result.IsLeaf() || !c.mem.readsMem(r.Result) {
		return
	}
	x, ok := strings.CutSuffix(r.Placement, ".Block")
	if !ok {
		return
	}
	inside := make(map[*rules.Value]bool)
	for _, o := range c.occs[x] {
		o.Walk(func(v *rules.Value) bool { inside[v] = true; return true })
	}
	for n, k := range c.nodes {
		if inside[n] || c.parent[n] == nil || isPhi(n) || !c.mem.readsMem(n) || c.mem.carriesMem(n.Op) || c.inBlock(k, c.place) {
			continue
		}
		name := n.Op.String()
		if rules.IsVarText(n.Name) {
			name = n.Name + " (" + name + ")"
		}
		c.report("result is placed at @%s, but the match also includes the load %s, which may be in a later block (after a bounds check, say); use @mergePoint(b, ...) over all the loads",
			r.Placement, name)
		return
	}
}
