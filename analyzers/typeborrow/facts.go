package typeborrow

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strconv"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// archFacts are facts about an arch's ops, derived from its own lowering
// rules (the arch's main rule set) rather than from a hand-written table.
type archFacts struct {
	// lshConst holds the ops that shift their single argument left by
	// their auxint, such as AMD64's SHLQconst and RISCV64's SLLI: the result
	// roots of rules like (SHLQ x (MOVQconst [c])) => (SHLQconst [c&63] x)
	// whose match root is a generic Lsh op or an op that lowers one.
	lshConst map[*ops.Op]bool
	// stores maps the ops that lower (Store {t} ptr val mem) && t.Size() == n
	// to n and to the index of val among their arguments.
	stores map[*ops.Op]store
	// ptrBytes is the pointer size, from the default type of the op that
	// lowers ConstNil; 0 if unknown.
	ptrBytes int
}

type store struct{ bytes, val int }

func deriveFacts(c *rules.Corpus) map[*ops.Arch]*archFacts {
	m := make(map[*ops.Arch]*archFacts)
	for _, s := range c.Sets {
		if s.Arch.Generic || s.Suffix != "" {
			continue
		}
		m[s.Arch] = deriveArch(s)
	}
	return m
}

func deriveArch(s *rules.RuleSet) *archFacts {
	f := &archFacts{lshConst: map[*ops.Op]bool{}, stores: map[*ops.Op]store{}}
	lowersLsh := map[*ops.Op]bool{}
	for _, r := range s.Rules {
		if r.IsBlock() || r.Result == nil || r.Result.IsLeaf() {
			continue
		}
		m, res := r.Match, r.Result
		switch {
		case m.Op.IsGeneric() && strings.HasPrefix(m.Op.Name, "Lsh"):
			// Arch ops that take the shifted value as their first argument.
			res.Walk(func(v *rules.Value) bool {
				if !v.IsLeaf() && !v.Op.IsGeneric() && len(v.Args) > 0 && len(m.Args) > 0 &&
					v.Args[0].IsVar() && v.Args[0].Name == m.Args[0].Name {
					lowersLsh[v.Op] = true
				}
				return true
			})
		case m.Op.Name == "ConstNil" && m.Op.IsGeneric():
			f.ptrBytes = typeBytes(res.Op.Typ)
		case m.Op.Name == "Store" && m.Op.IsGeneric() && len(m.Args) == 3 && m.Args[1].IsVar():
			n, ok := condSize(r.CondExpr, m.Aux)
			if !ok || res.Op.IsGeneric() {
				break
			}
			for i, a := range res.Args {
				if a.IsVar() && a.Name == m.Args[1].Name {
					f.stores[res.Op] = store{n, i}
				}
			}
		}
	}
	for _, r := range s.Rules {
		if r.IsBlock() || r.Result == nil || r.Result.IsLeaf() {
			continue
		}
		m, res := r.Match, r.Result
		if !(lowersLsh[m.Op] || m.Op.IsGeneric() && strings.HasPrefix(m.Op.Name, "Lsh")) || len(m.Args) != 2 {
			continue
		}
		k := m.Args[1]
		if k.IsLeaf() || len(k.Args) != 0 || !rules.IsVarText(k.AuxInt) {
			continue
		}
		if !res.Op.IsGeneric() && len(res.Args) == 1 && res.Args[0].IsVar() && res.Args[0].Name == m.Args[0].Name &&
			mentions(res.AuxInt, k.AuxInt) {
			f.lshConst[res.Op] = true
		}
	}
	// Stores with other addressing modes, such as
	// (MOVDstore [off] {sym} (ADD ptr idx) val mem) && ... => (MOVDstoreidx ptr idx val mem),
	// store the same bytes. Only rules that match a single store (its
	// memory is a variable) pass val through unchanged; store-combining
	// rules match a chain of stores. Ops derived inconsistently are dropped.
	for range 2 {
		derived := map[*ops.Op]store{}
		bad := map[*ops.Op]bool{}
		for _, r := range s.Rules {
			if r.IsBlock() || r.Result == nil || r.Result.IsLeaf() || r.Result.Op.IsGeneric() {
				continue
			}
			m, res := r.Match, r.Result
			st, ok := f.stores[m.Op]
			if _, known := f.stores[res.Op]; !ok || known || st.val >= len(m.Args) ||
				!m.Args[st.val].IsVar() || !m.Args[len(m.Args)-1].IsVar() || !res.Args[len(res.Args)-1].IsVar() {
				continue
			}
			for i, a := range res.Args {
				if a.IsVar() && a.Name == m.Args[st.val].Name {
					n := store{st.bytes, i}
					if d, ok := derived[res.Op]; ok && d != n {
						bad[res.Op] = true
					}
					derived[res.Op] = n
				}
			}
		}
		for op, n := range derived {
			if !bad[op] {
				f.stores[op] = n
			}
		}
	}
	return f
}

// mentions reports whether Go expression e uses identifier id.
func mentions(e, id string) bool {
	x, err := parser.ParseExpr(e)
	if err != nil {
		return false
	}
	found := false
	ast.Inspect(x, func(n ast.Node) bool {
		if i, ok := n.(*ast.Ident); ok && i.Name == id {
			found = true
		}
		return !found
	})
	return found
}

// condSize reports n if cond has a conjunct t.Size() == n.
func condSize(cond ast.Expr, t string) (int, bool) {
	for _, c := range conjuncts(cond) {
		if e, op, n, ok := sizeCompare(c); ok && op == token.EQL && e == t {
			return n, true
		}
	}
	return 0, false
}

// conjuncts splits e at top-level &&.
func conjuncts(e ast.Expr) []ast.Expr {
	switch x := e.(type) {
	case nil:
		return nil
	case *ast.ParenExpr:
		return conjuncts(x.X)
	case *ast.BinaryExpr:
		if x.Op == token.LAND {
			return append(conjuncts(x.X), conjuncts(x.Y)...)
		}
	}
	return []ast.Expr{e}
}

// sizeCompare matches E.Size() op N, with the operands in either order,
// returning E's text and the operator as if E were on the left.
func sizeCompare(e ast.Expr) (string, token.Token, int, bool) {
	b, ok := e.(*ast.BinaryExpr)
	if !ok {
		return "", 0, 0, false
	}
	op := b.Op
	x, y := b.X, b.Y
	if _, ok := y.(*ast.CallExpr); ok {
		x, y = y, x
		switch op {
		case token.LSS:
			op = token.GTR
		case token.GTR:
			op = token.LSS
		case token.LEQ:
			op = token.GEQ
		case token.GEQ:
			op = token.LEQ
		}
	}
	call, ok := x.(*ast.CallExpr)
	if !ok || len(call.Args) != 0 {
		return "", 0, 0, false
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Size" {
		return "", 0, 0, false
	}
	lit, ok := y.(*ast.BasicLit)
	if !ok || lit.Kind != token.INT {
		return "", 0, 0, false
	}
	n, err := strconv.Atoi(lit.Value)
	if err != nil {
		return "", 0, 0, false
	}
	return types.ExprString(sel.X), op, n, true
}

// typeBytes returns the size of an op default type name such as
// "UInt64", or 0.
func typeBytes(typ string) int {
	switch typ {
	case "Int8", "UInt8", "Bool":
		return 1
	case "Int16", "UInt16":
		return 2
	case "Int32", "UInt32", "Float32":
		return 4
	case "Int64", "UInt64", "Float64":
		return 8
	}
	return 0
}

// A site is the match node whose type a result's type expression names.
type site struct {
	expr   string       // the type expression: "t", "x.Type", or "v.Type"
	node   *rules.Value // the match node
	parent *rules.Value // node's parent in the match, or nil for the root
	idx    int          // node's index in parent.Args
}

// resolve returns the match node whose type expr denotes, if expr is a
// type variable bound in the match, x.Type for a value variable x bound in
// the match, or v.Type.
func resolve(r *rules.Rule, expr string) (site, bool) {
	s := site{expr: expr}
	vars := r.MatchVars()
	switch {
	case expr == "v.Type":
		s.node = r.Match // nil for a block rule
	case rules.IsVarText(expr):
		for _, o := range vars[expr] {
			if o.Kind == rules.OccType {
				s.node = o.Value
				break
			}
		}
	case strings.HasSuffix(expr, ".Type") && rules.IsVarText(strings.TrimSuffix(expr, ".Type")):
		for _, o := range vars[strings.TrimSuffix(expr, ".Type")] {
			if o.Kind == rules.OccValue {
				s.node = o.Value
				break
			}
		}
	}
	if s.node == nil {
		return s, false
	}
	for _, m := range r.MatchValues() {
		m.Walk(func(v *rules.Value) bool {
			for i, a := range v.Args {
				if a == s.node {
					s.parent, s.idx = v, i
				}
			}
			return true
		})
	}
	return s, true
}

// aliases returns the expressions that denote s's type in conditions.
func (s site) aliases(r *rules.Rule) []string {
	a := []string{s.expr}
	if s.node.Name != "" {
		a = append(a, s.node.Name+".Type")
	}
	if rules.IsVarText(s.node.Type) {
		a = append(a, s.node.Type)
	}
	if s.node == r.Match {
		a = append(a, "v.Type")
	}
	return a
}

// minBits returns a lower bound on the width in bits of s's type,
// considering only what the match and condition establish. Arch ops
// carry the types of the generic values they lower, which can be as
// narrow as 8 bits: Rsh8x64 lowers to RISCV64's SRAI with type int8.
func minBits(r *rules.Rule, s site, f *archFacts) int {
	bits := 8
	var o opsig.Operand
	if !s.node.IsLeaf() {
		if sig, ok := opsig.Lookup(s.node.Op); ok {
			o = sig.Result
		}
	} else if s.parent != nil {
		if sig, ok := opsig.Lookup(s.parent.Op); ok && s.idx < len(sig.Args) {
			o = sig.Args[s.idx]
		}
	}
	switch {
	case o.Width > 0:
		bits = o.Width
	case o.Kind == opsig.Ptr && f != nil && f.ptrBytes > 0:
		bits = 8 * f.ptrBytes
	}
	names := s.aliases(r)
	for _, c := range conjuncts(r.CondExpr) {
		if e, op, n, ok := sizeCompare(c); ok && contains(names, e) {
			switch op {
			case token.EQL, token.GEQ:
				bits = max(bits, 8*n)
			case token.GTR:
				bits = max(bits, 8*(n+1))
			}
			continue
		}
		// ssa.Is64BitInt(t), is32BitInt(t), ...
		if call, ok := c.(*ast.CallExpr); ok && len(call.Args) == 1 && contains(names, types.ExprString(call.Args[0])) {
			name := types.ExprString(call.Fun)
			name = strings.ToLower(name[strings.LastIndex(name, ".")+1:])
			for _, w := range []int{64, 32, 16} {
				if name == "is"+strconv.Itoa(w)+"bitint" || name == "is"+strconv.Itoa(w)+"bitfloat" {
					bits = max(bits, w)
				}
			}
		}
	}
	return bits
}

func contains(list []string, s string) bool {
	for _, x := range list {
		if x == s {
			return true
		}
	}
	return false
}

// describe says where s's type comes from, for diagnostics.
func (s site) describe(r *rules.Rule) string {
	if s.node.IsLeaf() {
		if s.parent != nil {
			return s.expr + " is the type of " + s.node.Name + ", argument " + strconv.Itoa(s.idx) + " of " + s.parent.Op.Name
		}
		return s.expr + " is the type of " + s.node.Name
	}
	if s.node == r.Match {
		return s.expr + " is the type of the matched " + s.node.Op.Name
	}
	return s.expr + " is the type of a matched " + s.node.Op.Name
}
