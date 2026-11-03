// Package flagscomplete checks that every flags consumer can absorb the
// pseudo-ops that may reach it: InvertFlags and the flag constants.
package flagscomplete

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "flagscomplete",
	Doc: `report flags consumers that can receive InvertFlags or a flag constant that no rule removes

InvertFlags and the flag constants (FlagEQ, FlagLT_ULT, FlagConstant, ...)
are pseudo-ops with no code generation: every op and block kind that
consumes flags must have rules that absorb them, or the compiler crashes
("InvertFlags should never make it to codegen").

For each rule that creates a flags consumer, flagscomplete works out what
the consumer's flags argument may become under the arch's other rules: a
compare that some rule canonicalizes into InvertFlags (CMP x y =>
(InvertFlags (CMP y x))), a compare of constants that some rule folds to a
flag constant, a flags variable taken from a consumer that itself absorbs
these pseudo-ops, or a Go expression such as ssa.FlagArg(b), which may be
any flags value. It reports the rule if the consumer has no rule for what
may arrive. For example, on ARM64

	((LessThan|...) (CMPconst [0] z:(MSUB a x y))) => ((LessThanNoov|...) (CMP a (MUL x y)))

creates LessThanNoov of a CMP, which can become InvertFlags, so without a
(LessThanNoov (InvertFlags x)) rule the compiler crashes.

Absorption is per auxint where the auxint is a constant: on PPC64,
(ISEL [2] x y (CMP a b)) needs a rule taking (ISEL [n] x y (InvertFlags
f)) with a condition that n == 2 satisfies, such as n%4 == 2.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		if set.Arch.Generic || set.Suffix != "" {
			continue
		}
		s := newState(set)
		if s == nil {
			continue
		}
		s.check(pass)
	}
	return nil
}

// consumer is an op or block kind that takes flags.
type consumer struct {
	op  *ops.Op
	blk *ops.Block
}

func (c consumer) String() string {
	if c.op != nil {
		return c.op.Name
	}
	return c.blk.Name
}

type state struct {
	set    *rules.RuleSet
	consts map[*ops.Op]bool // the flag constant ops

	// flagsArgs are the flags argument positions of consumers.
	flagsArgs map[consumer]map[int]bool
	// absorbs and folds record, for each consumer, the rules that take
	// InvertFlags and the rules for each flag constant (nil key: all, by
	// way of a helper that evaluates constant flags).
	absorbs map[consumer][]*rules.Rule
	folds   map[consumer]map[*ops.Op][]*rules.Rule

	// anyInv and anyConsts are the rules producing InvertFlags and each
	// flag constant: what an arbitrary flags value may become.
	anyInv    *rules.Rule
	anyConsts map[*ops.Op]*rules.Rule

	// dom is the auxints that rules may give each consumer, if known
	// (see findAuxDomains).
	dom map[consumer]map[int64]bool

	memo map[*rules.Value]*reach
}

// reach is what a flags-valued expression may become.
type reach struct {
	inv    string             // why it may become InvertFlags, or ""
	consts map[*ops.Op]string // flag constants it may become, and why
	busy   bool               // being computed
}

func newState(set *rules.RuleSet) *state {
	s := &state{set: set, consts: map[*ops.Op]bool{},
		flagsArgs: map[consumer]map[int]bool{}, absorbs: map[consumer][]*rules.Rule{},
		folds: map[consumer]map[*ops.Op][]*rules.Rule{}, memo: map[*rules.Value]*reach{},
		anyConsts: map[*ops.Op]*rules.Rule{}}
	// Flag constants are the arch's argumentless Flag* pseudo-ops, which
	// codegen rejects.
	for _, op := range set.Arch.Ops {
		if strings.HasPrefix(op.Name, "Flag") && op.ArgLength == 0 && op.Asm == "" {
			s.consts[op] = true
		}
	}
	if set.Arch.Op("InvertFlags") == nil && len(s.consts) == 0 {
		return nil
	}
	s.findFlagsArgs()
	s.findAbsorbers()
	s.findProduced()
	s.findAuxDomains()
	return s
}

// isFlags reports whether v is evidently a flags value.
func (s *state) isFlags(v *rules.Value) bool {
	if v.Op == nil {
		return false
	}
	if v.Op.Typ == "Flags" || v.Op.Name == "InvertFlags" || s.consts[v.Op] {
		return true
	}
	if (v.Op.Name == "Select1" || v.Op.Name == "Select0") && v.Op.IsGeneric() {
		if v.Type == "types.TypeFlags" {
			return true
		}
		if len(v.Args) == 1 && v.Args[0].Op != nil {
			if tt := v.Args[0].Op.TupleTypes(); len(tt) == 2 {
				i := 0
				if v.Op.Name == "Select1" {
					i = 1
				}
				return strings.TrimSpace(tt[i]) == "Flags"
			}
		}
	}
	return false
}

// findFlagsArgs finds the argument positions of ops and the control
// positions of blocks that hold flags in some rule: positions holding an
// evident flags value, and, iterating to a fixed point, positions to which
// a result passes a variable the match bound to flags. The latter find
// consumers that no rule matches with a flags expression, such as
// (CSEL [cc] (MOVDconst [-1]) (MOVDconst [0]) flag) => (CSETM [cc] flag).
func (s *state) findFlagsArgs() {
	changed := false
	add := func(c consumer, i int) {
		if s.flagsArgs[c] == nil {
			s.flagsArgs[c] = map[int]bool{}
		}
		if !s.flagsArgs[c][i] {
			s.flagsArgs[c][i] = true
			changed = true
		}
	}
	isFlags := s.isFlags
	for _, r := range s.set.Rules {
		walkSites(r, true, true, func(c consumer, _ string, args []*rules.Value) {
			for i, a := range args {
				if isFlags(a) {
					add(c, i)
				}
			}
		})
	}
	for changed {
		changed = false
		for _, r := range s.set.Rules {
			vars := s.flagsVars(r)
			if len(vars) == 0 {
				continue
			}
			walkSites(r, false, true, func(c consumer, _ string, args []*rules.Value) {
				for i, a := range args {
					if a.IsVar() && vars[a.Name] {
						add(c, i)
					}
				}
			})
		}
	}
}

// flagsVars returns the variables r's match binds to flags.
func (s *state) flagsVars(r *rules.Rule) map[string]bool {
	vars := map[string]bool{}
	walkSites(r, true, false, func(c consumer, _ string, args []*rules.Value) {
		for i := range s.flagsArgs[c] {
			if i < len(args) && args[i].IsVar() {
				vars[args[i].Name] = true
			}
		}
	})
	for _, top := range r.MatchValues() {
		top.Walk(func(v *rules.Value) bool {
			if v.Name != "" && v.Op != nil && s.isFlags(v) {
				vars[v.Name] = true
			}
			return true
		})
	}
	return vars
}

// walkSites calls f for each arch op and block in r's match and/or result
// with its auxint and its args or controls. InvertFlags is not a consumer.
func walkSites(r *rules.Rule, match, result bool, f func(c consumer, auxint string, args []*rules.Value)) {
	var tops []*rules.Value
	if match {
		tops = append(tops, r.MatchValues()...)
	}
	if result {
		tops = append(tops, r.ResultValues()...)
	}
	for _, top := range tops {
		top.Walk(func(v *rules.Value) bool {
			if v.Op != nil && !v.Op.IsGeneric() && v.Op.Name != "InvertFlags" && !v.Ellipsis {
				f(consumer{op: v.Op}, v.AuxInt, v.Args)
			}
			return true
		})
	}
	if !r.IsBlock() {
		return
	}
	if match && !r.MatchBlock.Info.IsGeneric() {
		f(consumer{blk: r.MatchBlock.Info}, r.MatchBlock.AuxInt, r.MatchBlock.Controls)
	}
	if result && !r.ResultBlock.Info.IsGeneric() {
		f(consumer{blk: r.ResultBlock.Info}, r.ResultBlock.AuxInt, r.ResultBlock.Controls)
	}
}

// findAbsorbers finds, for each consumer, the rules that take InvertFlags
// or flag constants in a flags position.
func (s *state) findAbsorbers() {
	for _, r := range s.set.Rules {
		var c consumer
		var args []*rules.Value
		if r.IsBlock() {
			c, args = consumer{blk: r.MatchBlock.Info}, r.MatchBlock.Controls
		} else if r.Match.Op != nil {
			c, args = consumer{op: r.Match.Op}, r.Match.Args
		}
		for i := range s.flagsArgs[c] {
			if i >= len(args) {
				continue
			}
			a := args[i]
			switch {
			case a.Op != nil && a.Op.Name == "InvertFlags":
				s.absorbs[c] = append(s.absorbs[c], r)
			case a.Op != nil && s.consts[a.Op]:
				s.fold(c, a.Op, r)
			case a.IsVar() && usedInCall(r, a.Name):
				// A helper like ccARM64Eval(cc, flag) evaluates any
				// constant flags.
				s.fold(c, nil, r)
			}
		}
	}
}

// findProduced finds the pseudo-ops that some rule produces.
func (s *state) findProduced() {
	for _, r := range s.set.Rules {
		for _, top := range r.ResultValues() {
			top.Walk(func(v *rules.Value) bool {
				switch {
				case v.Op == nil:
				case v.Op.Name == "InvertFlags":
					if s.anyInv == nil {
						s.anyInv = r
					}
				case s.consts[v.Op]:
					if s.anyConsts[v.Op] == nil {
						s.anyConsts[v.Op] = r
					}
				}
				return true
			})
		}
	}
}

func (s *state) fold(c consumer, k *ops.Op, r *rules.Rule) {
	if s.folds[c] == nil {
		s.folds[c] = map[*ops.Op][]*rules.Rule{}
	}
	s.folds[c][k] = append(s.folds[c][k], r)
}

// absorbed reports whether some rule removes InvertFlags from c with
// auxint aux ("" if unknown).
func (s *state) absorbed(c consumer, aux string) bool {
	return anyCovers(s.absorbs[c], aux)
}

// folded reports whether some rule folds constant k into c with auxint
// aux ("" if unknown).
func (s *state) folded(c consumer, k *ops.Op, aux string) bool {
	return anyCovers(s.folds[c][k], aux) || anyCovers(s.folds[c][nil], aux)
}

func anyCovers(rs []*rules.Rule, aux string) bool {
	for _, r := range rs {
		if coversAux(r, aux) {
			return true
		}
	}
	return false
}

// coversAux reports whether r's match may match its root with auxint aux.
// If aux is not an integer constant, or r's condition can't be evaluated,
// it reports true.
func coversAux(r *rules.Rule, aux string) bool {
	k, ok := intLit(aux)
	if !ok {
		return true
	}
	var m string
	if r.IsBlock() {
		m = r.MatchBlock.AuxInt
	} else {
		m = r.Match.AuxInt
	}
	switch {
	case m == "" || m == "_":
		return true
	case !rules.IsVarText(m):
		if lit, ok := intLit(m); ok {
			return lit == k
		}
		return true
	}
	return condMayHold(r, map[string]constant.Value{m: constant.MakeInt64(k)})
}

func intLit(s string) (int64, bool) {
	k, err := strconv.ParseInt(s, 0, 64)
	return k, err == nil
}

func conjuncts(e ast.Expr) []ast.Expr {
	if p, ok := e.(*ast.ParenExpr); ok {
		return conjuncts(p.X)
	}
	if b, ok := e.(*ast.BinaryExpr); ok && b.Op == token.LAND {
		return append(conjuncts(b.X), conjuncts(b.Y)...)
	}
	return []ast.Expr{e}
}

// eval evaluates an integer or boolean expression over the constants in
// env, such as n%4 == 2. It reports false for anything else.
func eval(e ast.Expr, env map[string]constant.Value) (constant.Value, bool) {
	switch e := e.(type) {
	case *ast.BasicLit:
		if e.Kind != token.INT {
			return nil, false
		}
		x := constant.MakeFromLiteral(e.Value, e.Kind, 0)
		return x, x.Kind() == constant.Int
	case *ast.Ident:
		x, ok := env[e.Name]
		return x, ok
	case *ast.ParenExpr:
		return eval(e.X, env)
	case *ast.CallExpr:
		// A conversion such as int32(c), which these small values survive.
		if id, ok := e.Fun.(*ast.Ident); ok && len(e.Args) == 1 && intTypes[id.Name] {
			return eval(e.Args[0], env)
		}
	case *ast.UnaryExpr:
		x, ok := eval(e.X, env)
		if !ok || e.Op != token.SUB && e.Op != token.NOT {
			return nil, false
		}
		return constant.UnaryOp(e.Op, x, 0), true
	case *ast.BinaryExpr:
		x, ok1 := eval(e.X, env)
		y, ok2 := eval(e.Y, env)
		if !ok1 || !ok2 || x.Kind() != y.Kind() {
			return nil, false
		}
		switch e.Op {
		case token.EQL, token.NEQ, token.LSS, token.LEQ, token.GTR, token.GEQ:
			return constant.MakeBool(constant.Compare(x, e.Op, y)), true
		case token.ADD, token.SUB, token.MUL, token.AND, token.OR, token.XOR, token.AND_NOT:
			return constant.BinaryOp(x, e.Op, y), x.Kind() == constant.Int
		case token.QUO, token.REM:
			if x.Kind() != constant.Int || constant.Sign(y) == 0 {
				return nil, false
			}
			op := e.Op
			if op == token.QUO {
				op = token.QUO_ASSIGN // integer division
			}
			return constant.BinaryOp(x, op, y), true
		case token.LAND, token.LOR:
			if x.Kind() != constant.Bool {
				return nil, false
			}
			return constant.BinaryOp(x, e.Op, y), true
		}
	}
	return nil, false
}

var intTypes = map[string]bool{"int": true, "int8": true, "int16": true, "int32": true, "int64": true,
	"uint": true, "uint8": true, "uint16": true, "uint32": true, "uint64": true}

// usedInCall reports whether name is an argument of a call in r's
// condition.
func usedInCall(r *rules.Rule, name string) bool {
	found := false
	if r.CondExpr == nil {
		return false
	}
	ast.Inspect(r.CondExpr, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			for _, a := range call.Args {
				if id, ok := a.(*ast.Ident); ok && id.Name == name {
					found = true
				}
			}
		}
		return true
	})
	return found
}

func where(r *rules.Rule) string {
	return fmt.Sprintf("%s:%d", filepath.Base(r.Pos.File), r.Pos.Line)
}

// reachOf returns what the flags-valued result expression v of rule r
// may become.
func (s *state) reachOf(r *rules.Rule, v *rules.Value) *reach {
	if x := s.memo[v]; x != nil {
		if x.busy {
			return &reach{}
		}
		return x
	}
	x := &reach{consts: map[*ops.Op]string{}, busy: true}
	s.memo[v] = x
	defer func() { x.busy = false }()
	switch {
	case v.Op == nil && !v.IsVar():
		// A Go expression, such as ssa.FlagArg(boolval): any flags value.
		if s.anyInv != nil {
			x.inv = fmt.Sprintf("it is %s, which may be any flags value, including InvertFlags (%s)", v.Name, where(s.anyInv))
		}
		for k, kr := range s.anyConsts {
			x.consts[k] = fmt.Sprintf("it is %s, which may be any flags value, including %s (%s)", v.Name, k.Name, where(kr))
		}
	case v.Op == nil:
		// A variable: it may be whatever its consumer in the match
		// may receive, as that consumer's own rules attest, or whatever
		// the match expression it names may become.
		if m := boundTo(r, v.Name); m != nil {
			y := s.reachOf(r, m)
			x.inv = y.inv
			for k, why := range y.consts {
				x.consts[k] = why
			}
			break
		}
		c, ok := s.boundUnder(r, v.Name)
		if !ok {
			return x
		}
		if ars := s.absorbs[c]; len(ars) > 0 {
			x.inv = fmt.Sprintf("%s is %s's flags, which may be InvertFlags (%s)", v.Name, c, where(ars[0]))
		}
		for k := range s.consts {
			if s.folded(c, k, "") {
				x.consts[k] = fmt.Sprintf("%s is %s's flags, which may be constant", v.Name, c)
			}
		}
	case v.Op.Name == "InvertFlags":
		x.inv = "it is InvertFlags"
	case s.consts[v.Op]:
		x.consts[v.Op] = "it is " + v.Op.Name
	default:
		for _, r2 := range s.set.Rules {
			if r2.IsBlock() || r2.Result == nil || r2.Match.Op != v.Op || !unify(v, r2.Match) {
				continue
			}
			y := s.reachOf(r2, r2.Result)
			if y.inv != "" && x.inv == "" {
				x.inv = fmt.Sprintf("%s becomes %s by %s", v.Op.Name, describe(r2.Result), where(r2))
				if r2.Result.Op == nil {
					x.inv += ", and " + y.inv
				}
			}
			for k, why := range y.consts {
				if _, ok := x.consts[k]; !ok {
					x.consts[k] = fmt.Sprintf("%s becomes %s by %s", v.Op.Name, describe(r2.Result), where(r2))
					if r2.Result.Op == nil {
						x.consts[k] += ", and " + why
					}
				}
			}
		}
	}
	return x
}

func describe(v *rules.Value) string {
	if v.Op == nil {
		return v.Name
	}
	return v.Op.Name
}

// boundTo returns the flags-valued op expression that r's match names
// name, as in x:(CMP a b), or nil.
func boundTo(r *rules.Rule, name string) *rules.Value {
	var found *rules.Value
	for _, top := range r.MatchValues() {
		top.Walk(func(v *rules.Value) bool {
			if found == nil && v.Op != nil && v.Name == name {
				found = v
			}
			return found == nil
		})
	}
	return found
}

// boundUnder returns the consumer in whose flags position r's match binds
// the variable name.
func (s *state) boundUnder(r *rules.Rule, name string) (consumer, bool) {
	var found consumer
	ok := false
	walkSites(r, true, false, func(c consumer, _ string, args []*rules.Value) {
		for i := range s.flagsArgs[c] {
			if i < len(args) && args[i].Op == nil && args[i].Name == name {
				found, ok = c, true
			}
		}
	})
	return found, ok
}

// unify reports whether the result expression v could match pattern m,
// ignoring aux fields and conditions.
func unify(v, m *rules.Value) bool {
	if m.Op == nil || v.Op == nil {
		return true
	}
	if m.Op != v.Op {
		return false
	}
	if m.Ellipsis {
		return true
	}
	for _, mc := range rules.Commutations(m) {
		if len(mc.Args) > len(v.Args) || len(mc.Args) < len(v.Args) && !mc.Rest {
			continue
		}
		ok := true
		for i := range mc.Args {
			if !unify(v.Args[i], mc.Args[i]) {
				ok = false
				break
			}
		}
		if ok {
			return true
		}
	}
	return false
}

type problem struct {
	c   consumer
	aux string
	inv bool
}

func (s *state) check(pass *analysis.Pass) {
	seen := map[problem]bool{}
	for _, r := range s.set.Rules {
		walkSites(r, false, true, func(c consumer, auxText string, args []*rules.Value) {
			if len(s.flagsArgs[c]) == 0 {
				return
			}
			// The auxints the site may have, if they are known
			// constants; "" stands for unknown.
			auxes := []string{""}
			if ks, ok := s.auxValues(r, auxText); ok && c.hasAuxInt() {
				auxes = auxes[:0]
				for _, k := range ks {
					auxes = append(auxes, strconv.FormatInt(k, 10))
				}
			}
			var pos []int
			for i := range s.flagsArgs[c] {
				pos = append(pos, i)
			}
			sort.Ints(pos)
			for _, i := range pos {
				if i >= len(args) {
					continue
				}
				x := s.reachOf(r, args[i])
				for _, aux := range auxes {
					s.report(pass, r, seen, c, aux, auxText, x)
				}
			}
		})
	}
}

// report reports what may reach c with auxint aux and has no rule.
func (s *state) report(pass *analysis.Pass, r *rules.Rule, seen map[problem]bool, c consumer, aux, auxText string, x *reach) {
	name := c.String()
	switch {
	case aux == "":
	case aux == auxText || auxText == "":
		name += " [" + aux + "]"
	default:
		name += fmt.Sprintf(" [%s] (with %s = %s)", auxText, auxText, aux)
	}
	p := problem{c, aux, true}
	if x.inv != "" && !s.absorbed(c, aux) && !seen[p] {
		seen[p] = true
		pass.Reportf(r.Pos, "%s's flags may be InvertFlags (%s), but no rule absorbs InvertFlags into %s, which codegen rejects", name, x.inv, c.withAux(aux))
	}
	var names []string
	why := ""
	for k, w := range x.consts {
		if !s.folded(c, k, aux) {
			names = append(names, k.Name)
			if why == "" || w < why {
				why = w
			}
		}
	}
	p.inv = false
	if len(names) > 0 && !seen[p] {
		seen[p] = true
		sort.Strings(names)
		pass.Reportf(r.Pos, "%s's flags may be %s (%s), but no rule folds them into %s, and codegen rejects flag constants", name, strings.Join(names, ", "), why, c.withAux(aux))
	}
}

// hasAuxInt reports whether c's values or blocks have an integer auxint.
func (c consumer) hasAuxInt() bool {
	if c.op != nil {
		return c.op.HasAuxInt
	}
	return c.blk.AuxIntType != "" && c.blk.AuxIntType != "invalid"
}

func (c consumer) withAux(aux string) string {
	if aux == "" {
		return c.String()
	}
	return c.String() + " [" + aux + "]"
}

// maxDomain bounds the auxint domains findAuxDomains tracks.
const maxDomain = 64

// findAuxDomains computes, for each consumer, the auxints that rules may
// give it: constants, and functions of auxints bound in the match whose
// own domains are known. On PPC64, (CondSelect x y (SETBC [a] cmp)) =>
// (ISEL [a] x y cmp) gives ISEL the auxints that SETBC has, 0, 1, and 2.
// A consumer that some rule gives any other auxint has no domain.
func (s *state) findAuxDomains() {
	s.dom = map[consumer]map[int64]bool{}
	for _, r := range s.set.Rules {
		walkSites(r, false, true, func(c consumer, _ string, _ []*rules.Value) {
			s.dom[c] = map[int64]bool{}
		})
	}
	unknown := map[consumer]bool{}
	for changed := true; changed; {
		changed = false
		for _, r := range s.set.Rules {
			walkSites(r, false, true, func(c consumer, auxText string, _ []*rules.Value) {
				if unknown[c] {
					return
				}
				ks, ok := s.auxValues(r, auxText)
				for _, k := range ks {
					if !s.dom[c][k] {
						s.dom[c][k] = true
						changed = true
					}
				}
				if !ok || len(s.dom[c]) > maxDomain {
					unknown[c] = true
					delete(s.dom, c)
					changed = true
				}
			})
		}
	}
	for c := range unknown {
		delete(s.dom, c)
	}
}

// auxValues returns the values that the result auxint text of rule r may
// take, given the domains computed so far.
func (s *state) auxValues(r *rules.Rule, text string) ([]int64, bool) {
	if text == "" {
		return []int64{0}, true // results reset auxints
	}
	if k, ok := intLit(text); ok {
		return []int64{k}, true
	}
	e, err := parser.ParseExpr(text)
	if err != nil {
		return nil, false
	}
	var free []string
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.CallExpr:
			if id, ok := n.Fun.(*ast.Ident); ok && intTypes[id.Name] {
				for _, a := range n.Args {
					ast.Inspect(a, func(n ast.Node) bool {
						if id, ok := n.(*ast.Ident); ok {
							free = append(free, id.Name)
						}
						return true
					})
				}
				return false
			}
		case *ast.Ident:
			free = append(free, n.Name)
		}
		return true
	})
	if len(free) != 1 {
		return nil, false
	}
	src, ok := auxBinder(r, free[0])
	if !ok {
		return nil, false
	}
	dom := s.dom[src]
	if dom == nil {
		return nil, false
	}
	var ks []int64
	for k := range dom {
		env := map[string]constant.Value{free[0]: constant.MakeInt64(k)}
		if !condMayHold(r, env) {
			continue
		}
		x, ok := eval(e, env)
		if !ok || x.Kind() != constant.Int {
			return nil, false
		}
		v, exact := constant.Int64Val(x)
		if !exact {
			return nil, false
		}
		ks = append(ks, v)
	}
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
	return ks, true
}

// auxBinder returns the arch op or block whose auxint r's match binds to
// the variable name.
func auxBinder(r *rules.Rule, name string) (consumer, bool) {
	var found consumer
	ok := false
	walkSites(r, true, false, func(c consumer, auxText string, _ []*rules.Value) {
		if !ok && auxText == name {
			found, ok = c, true
		}
	})
	return found, ok
}

// condMayHold reports whether r's condition may hold given env: whether
// no conjunct that can be evaluated is false.
func condMayHold(r *rules.Rule, env map[string]constant.Value) bool {
	if r.CondExpr == nil {
		return true
	}
	for _, e := range conjuncts(r.CondExpr) {
		if x, ok := eval(e, env); ok && x.Kind() == constant.Bool && !constant.BoolVal(x) {
			return false
		}
	}
	return true
}
