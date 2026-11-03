// Package ptrtype reports result values whose pointerness is wrong: a
// pointer typed as a non-pointer, or a non-pointer typed as a pointer.
package ptrtype

import (
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "ptrtype",
	Doc: `report result values whose type gets pointerness wrong

The GC, stack copying, and write barriers find pointers by SSA type.
A pointer value with a non-pointer type is invisible to them; a
non-pointer value with a pointer type is a bad pointer when live across
a safepoint. ptrtype reports:

  - An address op (OffPtr, AddPtr, Addr, ...) typed with an element type
    rather than a pointer to it, such as the type {t} of a Store or
    t.FieldType(0). generic.rules once had
    (Store {t2} (OffPtr <t2.(*types.Type)> [o2] dst) d1 ...) (c96e3bcc97)
    and (OffPtr <t.FieldType(0)> [0] dst) (945180fe2a).

  - Non-address arithmetic (a subtraction, comparison, xor, ...) typed
    with the type of a pointer operand. RISCV64 had
    (EqPtr x y) => (SEQZ (SUB <x.Type> x y)), a pointer difference typed
    as a pointer; fixed by 1ed30ca537.

  - An intermediate typed with the matched value's possibly-pointer type
    that omits the matched pointer operand, so it holds an offset or other
    non-pointer. AMD64latelower had
    (LEAQ1 <t> [c] {s} x y) && isPtr(x.Type) && c != 0 && s == nil
      => (ADDQ x (ADDQconst <t> [c] y));
    y+c is not a pointer (f9cf2c4d04, reverted by 96d2e41617).

  - A pointer-width add that folds away a constant operand that may be
    a typed nil without checking !t.IsPtr(), such as
    (ADD x (MOVDconst [c])) => (ADDconst [c] x): for nil+x the pointer
    type of the result is lost when (ADDconst [0] x) => x fires.
    Fixed on all arches by 21f434058c.

Op roles (address arithmetic, integer-only ops, the nil constant) are
derived from each arch's lowering of the generic ops.`,
	Run: run,
}

// archFacts are op roles derived from an arch's lowering rules.
type archFacts struct {
	// addrOps are the result roots of lowering generic ops that produce
	// a pointer or a value of any type (AddPtr, OffPtr, Addr, Load,
	// CondSelect, ...): ops whose values may be pointers.
	addrOps map[*ops.Op]bool
	// intOps are the result roots of lowering generic ops that produce
	// integers or booleans, minus addrOps: ops whose values are never
	// pointers.
	intOps map[*ops.Op]bool
	// addPtr are the ops that lower AddPtr.
	addPtr map[*ops.Op]bool
	// constNil is the op that lowers ConstNil.
	constNil *ops.Op
}

func deriveFacts(c *rules.Corpus) map[*ops.Arch]*archFacts {
	m := make(map[*ops.Arch]*archFacts)
	for _, s := range c.Sets {
		if s.Arch.Generic || s.Suffix != "" {
			continue
		}
		f := &archFacts{addrOps: map[*ops.Op]bool{}, intOps: map[*ops.Op]bool{}, addPtr: map[*ops.Op]bool{}}
		for _, r := range s.Rules {
			if r.IsBlock() || r.Result == nil || r.Result.IsLeaf() || !r.Match.Op.IsGeneric() || r.Result.Op.IsGeneric() {
				continue
			}
			sig, ok := opsig.Lookup(r.Match.Op)
			if !ok {
				continue
			}
			op := r.Result.Op
			switch sig.Result.Kind {
			case opsig.Ptr, opsig.Any:
				f.addrOps[op] = true
			case opsig.Int, opsig.Bool:
				f.intOps[op] = true
			}
			switch r.Match.Op.Name {
			case "AddPtr":
				f.addPtr[op] = true
			case "ConstNil":
				f.constNil = op
			}
		}
		for op := range f.addrOps {
			delete(f.intOps, op)
		}
		m[s.Arch] = f
	}
	return m
}

func run(pass *analysis.Pass) error {
	facts := deriveFacts(pass.Corpus)
	for r := range pass.Rules() {
		f := facts[r.Set.Arch]
		for _, res := range r.ResultValues() {
			res.Walk(func(v *rules.Value) bool {
				if v.IsLeaf() {
					return false
				}
				if !elementTyped(pass, r, v) && !nonAddrPtr(pass, r, f, v) && v != r.Result {
					excludesPtr(pass, r, f, v)
				}
				return true
			})
		}
		nilFold(pass, r, f)
	}
	return nil
}

// elementTyped reports an address op typed with an element type.
func elementTyped(pass *analysis.Pass, r *rules.Rule, v *rules.Value) bool {
	if v.Type == "" || !producesPtr(v.Op) {
		return false
	}
	if why := elementType(r, v.Type); why != "" {
		pass.Reportf(r.Pos, "%s produces a pointer but is typed <%s>, %s; use a pointer type such as <%s.PtrTo()>",
			v.Op.Name, v.Type, why, v.Type)
		return true
	}
	return false
}

// producesPtr reports whether op's result is always an address: a generic
// op whose result is a pointer, or an arch op that takes a symbol's address.
func producesPtr(op *ops.Op) bool {
	if sig, ok := opsig.Lookup(op); ok {
		return sig.Result.Kind == opsig.Ptr && op.Name != "ConstNil"
	}
	return !op.IsGeneric() && op.SymEffect == "Addr"
}

// elementType reports why type expression expr denotes the type of a
// pointed-to element rather than a pointer, or "".
func elementType(r *rules.Rule, expr string) string {
	e, err := parser.ParseExpr(expr)
	if err != nil {
		return ""
	}
	for {
		switch x := e.(type) {
		case *ast.ParenExpr:
			e = x.X
			continue
		case *ast.TypeAssertExpr: // t.(*types.Type), in older rules
			e = x.X
			continue
		case *ast.CallExpr:
			if id, ok := x.Fun.(*ast.Ident); ok && id.Name == "auxToType" && len(x.Args) == 1 {
				e = x.Args[0]
				continue
			}
			if sel, ok := x.Fun.(*ast.SelectorExpr); ok {
				switch sel.Sel.Name {
				case "Elem", "FieldType":
					// The FieldType of a call's type is the type of a result,
					// such as the unsafe.Pointer of runtime.makeslice.
					if s, ok := resolve(r, types.ExprString(sel.X)); ok && !s.node.IsLeaf() {
						if sig, ok := opsig.Lookup(s.node.Op); ok && sig.Result.Kind == opsig.Results {
							return ""
						}
					}
					return "the type of an element, not a pointer"
				}
			}
		case *ast.Ident:
			for _, o := range r.MatchVars()[x.Name] {
				if o.Kind == rules.OccAux && o.Value != nil && strings.HasPrefix(o.Value.Op.Aux, "Typ") {
					return "and " + x.Name + " is the type " + o.Value.Op.Name + " {" + x.Name + "} stores, not a pointer to it"
				}
			}
		}
		return ""
	}
}

// nonAddrPtr reports a non-address op typed with a pointer operand's type.
func nonAddrPtr(pass *analysis.Pass, r *rules.Rule, f *archFacts, v *rules.Value) bool {
	if v.Type == "" {
		return false
	}
	s, ok := resolve(r, v.Type)
	if !ok || !s.isPtr() || negatedPtrCheck(r, s.aliases(r)) {
		return false
	}
	// Arithmetic on two pointers, such as their difference, is not a
	// pointer even when the op can do address arithmetic.
	nptr := 0
	for _, a := range v.Args {
		if a.IsVar() {
			if as, ok := resolve(r, a.Name+".Type"); ok && as.isPtr() {
				nptr++
			}
		}
	}
	if !neverPtr(f, v.Op) && nptr < 2 {
		return false
	}
	pass.Reportf(r.Pos, "%s computes a non-pointer but is typed <%s>, and %s, a pointer; a live %s would be a bad pointer to the GC; use typ.Uintptr",
		v.Op.Name, v.Type, s.describe(r), v.Op.Name)
	return true
}

// neverPtr reports whether op never produces a pointer.
func neverPtr(f *archFacts, op *ops.Op) bool {
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		if !ok {
			return false
		}
		switch sig.Result.Kind {
		case opsig.Bool:
			return true
		case opsig.Int:
			// Rules type integer adds of pointers as pointers; AddPtr is the
			// canonical form, but leave adds alone.
			return !strings.HasPrefix(op.Name, "Add")
		}
		return false
	}
	return f != nil && f.intOps[op]
}

// excludesPtr reports an intermediate typed with the matched root's type,
// which may be a pointer, that does not contain the root's pointer operand.
func excludesPtr(pass *analysis.Pass, r *rules.Rule, f *archFacts, v *rules.Value) {
	if r.IsBlock() || v.Type == "" {
		return
	}
	root := r.Match
	names := []string{"v.Type"}
	if rules.IsVarText(root.Type) {
		names = append(names, root.Type)
	}
	if !contains(names, v.Type) || !maybePtr(f, root.Op) || negatedPtrCheck(r, names) {
		return
	}
	// The root's operands that may be the pointer.
	var ptrs, pinned []string
	sig, hasSig := opsig.Lookup(root.Op)
	for i, a := range root.Args {
		if !a.IsVar() {
			continue
		}
		if hasSig && i < len(sig.Args) && sig.Args[i].Kind != opsig.Ptr && sig.Args[i].Kind != opsig.Any {
			continue
		}
		aliases := []string{a.Name + ".Type"}
		if negatedPtrCheck(r, aliases) {
			continue
		}
		ptrs = append(ptrs, a.Name)
		if ptrCheck(r, aliases) {
			pinned = append(pinned, a.Name)
		}
	}
	if len(pinned) > 0 {
		ptrs = pinned
	}
	if len(ptrs) == 0 {
		return
	}
	leaves := map[string]bool{}
	v.Walk(func(w *rules.Value) bool {
		if w.IsLeaf() {
			leaves[w.Name] = true
		}
		return true
	})
	for _, p := range ptrs {
		if leaves[p] {
			return
		}
	}
	pass.Reportf(r.Pos, "(%s <%s> ...) is typed like the matched %s, which may be a pointer, but does not contain its pointer operand %s; the intermediate is not a valid pointer, so give it a non-pointer type or guard with !%s.IsPtr()",
		v.Op.Name, v.Type, root.Op.Name, strings.Join(ptrs, " or "), names[len(names)-1])
}

// maybePtr reports whether values of op may be pointers: generic pointer
// ops, the ops that lower AddPtr, and address computations (LEAQ1, ...).
func maybePtr(f *archFacts, op *ops.Op) bool {
	if sig, ok := opsig.Lookup(op); ok {
		return sig.Result.Kind == opsig.Ptr
	}
	return !op.IsGeneric() && (op.SymEffect == "Addr" || f != nil && f.addPtr[op])
}

// nilFold reports pointer-width adds that lose the pointer type of a
// constant operand that may be a typed nil (ConstNil lowers to the arch's
// integer constant op, keeping its pointer type). Either
//
//   - the rule folds the constant into an op F, as in
//     (ADD x (MOVDconst [c])) => (ADDconst [c] x), without checking
//     !t.IsPtr() for the constant's type, and the rule set also has
//     (F [0] x) => x, which then replaces nil+x by the integer x; or
//   - the rule rebuilds the constant without a type, as in
//     (I64Add (I64Const [x]) y) => (I64Add y (I64Const [x])), resetting it
//     to the op's integer default type, so a later !t.IsPtr() check passes.
func nilFold(pass *analysis.Pass, r *rules.Rule, f *archFacts) {
	if f == nil || f.constNil == nil || r.IsBlock() || r.Result == nil || r.Result.IsLeaf() || !f.addPtr[r.Match.Op] {
		return
	}
	for _, c := range r.Match.Args {
		if c.IsLeaf() || c.Op != f.constNil {
			continue
		}
		if !rules.IsVarText(c.AuxInt) && c.AuxInt != "0" {
			continue // a nonzero constant is not nil
		}
		if rules.IsVarText(c.Type) && negatedPtrCheck(r, []string{c.Type}) {
			continue
		}
		if c.Name != "" && usesName(r.Result, c.Name) {
			continue
		}
		var rebuilt *rules.Value
		r.Result.Walk(func(w *rules.Value) bool {
			if !w.IsLeaf() && w.Op == c.Op && w.Type == "" && w.AuxInt == c.AuxInt {
				rebuilt = w
			}
			return rebuilt == nil
		})
		if rebuilt != nil {
			pass.Reportf(r.Pos, "the matched %s may be a typed nil (ConstNil lowers to it), but the result rebuilds it as (%s [%s]) with %s's default type %s, so nil+x loses its pointer type and later !t.IsPtr() checks on the constant pass; keep the matched value (bind it, c:(%s [%s])) instead",
				c.Op.Name, c.Op.Name, c.AuxInt, c.Op.Name, c.Op.Typ, c.Op.Name, c.AuxInt)
			return
		}
		if id := identity(r.Set, r.Result.Op); id != nil {
			pass.Reportf(r.Pos, "%s of a %s, which may be a typed nil (ConstNil lowers to it), is folded into %s without a !t.IsPtr() check on (%s <t> ...); with %s:%d, (%s [0] x) => x, nil+x becomes the integer x and loses its pointer type",
				r.Match.Op.Name, c.Op.Name, r.Result.Op.Name, c.Op.Name, shortFile(id.Pos.File), id.Pos.Line, r.Result.Op.Name)
			return
		}
	}
}

// identity returns a rule of set of the form (op [0] x) => x, or nil.
func identity(set *rules.RuleSet, op *ops.Op) *rules.Rule {
	for _, r := range set.ByOp[op] {
		m := r.Match
		if m.AuxInt == "0" && len(m.Args) == 1 && m.Args[0].IsVar() && r.Result != nil && r.Result.IsVar() && r.Result.Name == m.Args[0].Name {
			return r
		}
	}
	return nil
}

func shortFile(p string) string { return p[strings.LastIndex(p, "/")+1:] }

func usesName(v *rules.Value, name string) bool {
	found := false
	v.Walk(func(w *rules.Value) bool {
		if w.Name == name {
			found = true
		}
		return !found
	})
	return found
}

// ptrCheck reports whether r's condition requires one of the type
// expressions in names to be a pointer: isPtr(t), t.IsPtr(), t.IsPtrShaped().
func ptrCheck(r *rules.Rule, names []string) bool {
	for _, c := range conjuncts(r.CondExpr) {
		if isPtrCall(c, names) {
			return true
		}
	}
	return false
}

// negatedPtrCheck is like ptrCheck for !isPtr(t) and the like.
func negatedPtrCheck(r *rules.Rule, names []string) bool {
	for _, c := range conjuncts(r.CondExpr) {
		if u, ok := c.(*ast.UnaryExpr); ok && u.Op == token.NOT && isPtrCall(u.X, names) {
			return true
		}
	}
	return false
}

func isPtrCall(e ast.Expr, names []string) bool {
	for {
		p, ok := e.(*ast.ParenExpr)
		if !ok {
			break
		}
		e = p.X
	}
	call, ok := e.(*ast.CallExpr)
	if !ok {
		return false
	}
	switch fn := call.Fun.(type) {
	case *ast.Ident:
		return fn.Name == "isPtr" && len(call.Args) == 1 && contains(names, types.ExprString(call.Args[0]))
	case *ast.SelectorExpr:
		switch fn.Sel.Name {
		case "IsPtr", "IsPtrShaped", "IsUnsafePtr":
			return len(call.Args) == 0 && contains(names, types.ExprString(fn.X))
		}
	}
	return false
}

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

func contains(list []string, s string) bool {
	for _, x := range list {
		if x == s {
			return true
		}
	}
	return false
}

// A site is the match node whose type a result's type expression names.
type site struct {
	expr   string
	node   *rules.Value
	parent *rules.Value
	idx    int
}

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

// isPtr reports whether the generic ops of the match make s a pointer:
// a generic op producing a pointer, or an operand in a pointer position
// of a generic op (EqPtr's operands, Load's address, ...).
func (s site) isPtr() bool {
	var o opsig.Operand
	if !s.node.IsLeaf() {
		sig, ok := opsig.Lookup(s.node.Op)
		if !ok || s.node.Op.Name == "ConstNil" {
			return false
		}
		o = sig.Result
	} else if s.parent != nil {
		sig, ok := opsig.Lookup(s.parent.Op)
		if !ok || s.idx >= len(sig.Args) {
			return false
		}
		o = sig.Args[s.idx]
	}
	return o.Kind == opsig.Ptr
}

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

func (s site) describe(r *rules.Rule) string {
	if s.node.IsLeaf() && s.parent != nil {
		return s.expr + " is the type of " + s.node.Name + ", an address operand of " + s.parent.Op.Name
	}
	return s.expr + " is the type of a matched " + s.node.Op.Name
}
