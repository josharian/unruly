package rulelint

import (
	"go/ast"
	"go/token"
	"go/types"
	"strings"

	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// resultExprs returns the condition and the result's Go expressions:
// everywhere a match variable can be used.
func (c *checker) resultExprs() []ast.Expr {
	var es []ast.Expr
	for _, e := range []ast.Expr{c.tr.Cond, c.tr.Code, c.tr.Placement} {
		if e != nil {
			es = append(es, e)
		}
	}
	add := func(node any, fields ...typecheck.Field) {
		for _, f := range fields {
			if e := c.tr.Expr(node, f); e != nil {
				es = append(es, e)
			}
		}
	}
	for _, v := range c.rule.ResultValues() {
		v.Walk(func(v *rules.Value) bool {
			add(v, typecheck.Type, typecheck.AuxInt, typecheck.Aux)
			if v.IsLeaf() {
				add(v, typecheck.Name)
			}
			return true
		})
	}
	if c.rule.IsBlock() {
		add(c.rule.ResultBlock, typecheck.AuxInt, typecheck.Aux)
	}
	return es
}

// variadicArity reports a match of a variadic op with a fixed list of
// args, all of them variables used nowhere else (or _). A fixed list
// constrains the arg count, which unused names suggest was not meant:
// (IMake _typ (StructMake val)) => imakeOfStructMake(v) never fires for
// structs of two or more fields, but (StructMake ___) does. (A list in
// which some arg is used, such as (StaticLECall {f} x y mem), is
// evidently meant to match a particular call shape.)
func (c *checker) variadicArity() {
	vars := c.rule.MatchVars()
	used := c.resultExprs()
	for _, m := range c.rule.MatchValues() {
		m.Walk(func(v *rules.Value) bool {
			if v.Op == nil || v.Op.ArgLength != -1 || v.Rest || v.Ellipsis || len(v.Args) == 0 {
				return true
			}
			var names []string
			for _, a := range v.Args {
				switch {
				case a.Name == "_":
				case a.IsVar() && len(vars[a.Name]) == 1 && !uses(used, a.Name):
					names = append(names, a.Name)
				default:
					return true
				}
			}
			if len(names) > 0 {
				c.report("%s is variadic, so %s matches only %s with exactly %d args, but %s is otherwise unused; did you mean (%s ___)?",
					v.OpName, v.Text, v.OpName, len(v.Args), strings.Join(names, ", "), v.OpName)
			}
			return true
		})
	}
}

// mergeSym reports a condition that applies a predicate to only one of
// the symbols merged by the result's mergeSym(sym1, sym2). The merged
// symbol is whichever is non-nil, usually sym2, so a test of sym1 alone,
// like !isAuto(sym1), checks the wrong symbol.
func (c *checker) mergeSym() {
	if c.tr.Cond == nil {
		return
	}
	var pairs [][2]string
	for _, e := range c.exprs() {
		ast.Inspect(e, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if ok && isMergeSym(call) && len(call.Args) == 2 {
				x, ok1 := call.Args[0].(*ast.Ident)
				y, ok2 := call.Args[1].(*ast.Ident)
				if ok1 && ok2 {
					pairs = append(pairs, [2]string{x.Name, y.Name})
				}
			}
			return true
		})
	}
	for _, p := range pairs {
		// For each predicate, which of the pair it is applied to.
		applied := map[string][2]bool{}
		var calls []*ast.CallExpr
		ast.Inspect(c.tr.Cond, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok {
				return true
			}
			if isMergeSym(call) || strings.EqualFold(funcName(call), "canMergeSym") {
				return false
			}
			f := funcName(call)
			for _, a := range call.Args {
				id, ok := a.(*ast.Ident)
				if !ok {
					continue
				}
				for i, s := range p {
					if id.Name == s {
						got := applied[f]
						if !got[0] && !got[1] {
							calls = append(calls, call)
						}
						got[i] = true
						applied[f] = got
					}
				}
			}
			return true
		})
		for _, call := range calls {
			got := applied[funcName(call)]
			if got[0] != got[1] {
				c.report("condition tests %s on only one of the symbols merged by mergeSym(%s, %s); test both, or mergeSym(%[2]s, %[3]s)",
					str(call), p[0], p[1])
			}
		}
	}
}

func isMergeSym(call *ast.CallExpr) bool {
	return strings.EqualFold(funcName(call), "mergeSym")
}

// emptyMake reports a result StructMake or ArrayMake1 of the rewritten
// value's own type without a t.Size() > 0 guard. A zero-sized aggregate
// must be (Empty); check.go rejects a zero-sized Make. (Before the Empty
// op existed, zero-sized Makes were legal.) For example,
// (Load <t> ptr mem) && t.IsArray() && t.NumElem() == 1 && CanSSA(t)
// => (ArrayMake1 (Load <t.Elem()> ptr mem)) fires for [1]struct{}.
func (c *checker) emptyMake() {
	r := c.rule
	if r.Result == nil || r.Result.Op == nil {
		return
	}
	switch r.Result.OpName {
	case "StructMake", "ArrayMake1":
	default:
		return
	}
	switch r.Match.OpName {
	case "StructMake", "ArrayMake1":
		return // the matched value is a non-empty aggregate
	}
	if r.Set.Arch.Tables().Generic.Op("Empty") == nil {
		return
	}
	names := []string{"v.Type"}
	if rules.IsVarText(r.Match.Type) {
		names = append(names, r.Match.Type)
	}
	if r.Match.Name != "" {
		names = append(names, r.Match.Name+".Type")
	}
	typ, src := r.ResultType(r.Result)
	if src != rules.TypeInherited && !(src == rules.TypeExplicit && contains(names, typ)) {
		return
	}
	for _, e := range c.conjuncts() {
		b, ok := ast.Unparen(e).(*ast.BinaryExpr)
		if !ok {
			continue
		}
		size, k, op := b.X, b.Y, b.Op
		if c.constInt(k) != 0 {
			size, k, op = b.Y, b.X, mirror(op)
		}
		name, ok := sizeOf(size)
		if ok && contains(names, name) && c.constInt(k) == 0 && (op == token.GTR || op == token.NEQ) {
			return
		}
	}
	c.report("%s of the rewritten value's type needs a %s.Size() > 0 condition: a zero-sized aggregate must be (Empty)",
		r.Result.OpName, names[len(names)-1])
}

func contains(list []string, s string) bool {
	for _, x := range list {
		if x == s {
			return true
		}
	}
	return false
}

// ptrShaped reports decomposition shortcuts like (StructMake x) &&
// x.Type.IsPtr() => x. Single-element aggregates are direct-interface
// (stored in the interface data word) when their element is pointer-shaped,
// which includes maps, chans, and funcs, not only pointers.
func (c *checker) ptrShaped() {
	r := c.rule
	if r.Result == nil || !r.Result.IsVar() || r.Match.Op == nil || r.Match.Op.Arch != r.Set.Arch.Tables().Generic {
		return
	}
	switch r.Match.OpName {
	case "StructMake", "StructMake1", "ArrayMake1", "StructSelect", "ArraySelect":
	default:
		return
	}
	for _, e := range c.conjuncts() {
		call, ok := ast.Unparen(e).(*ast.CallExpr)
		if !ok || len(call.Args) != 0 {
			continue
		}
		if sel, ok := call.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "IsPtr" {
			c.report("%s misses maps, chans, and funcs, which are also direct-interface; use IsPtrShaped()", str(call))
		}
	}
}

// synthSym reports a result symbol computed by a helper from something
// other than symbols, such as {ptrElem(s, off)}, that is not given the
// function (b.Func, b, or v). Such a helper refers to a new linker symbol,
// whose use must be recorded on the function (for example with
// reflectdata.MarkTypeSymUsedInInterface), or the linker's dead code
// elimination may drop what it needs.
func (c *checker) synthSym() {
	for _, rv := range c.rule.ResultValues() {
		rv.Walk(func(v *rules.Value) bool {
			if v.Op == nil || !strings.Contains(v.Op.Aux, "Sym") {
				return true
			}
			call, ok := ast.Unparen(c.tr.Expr(v, typecheck.Aux)).(*ast.CallExpr)
			if !ok || !c.isPkgFunc(call) {
				return true
			}
			symType := c.res.Info.TypeOf(call)
			onlySyms := true
			for _, a := range call.Args {
				t := c.res.Info.TypeOf(a)
				if isFuncContext(t) {
					return true
				}
				if t == nil || symType == nil || !types.Identical(t, symType) {
					onlySyms = false
				}
			}
			if onlySyms {
				return true // chooses among existing symbols, like mergeSym
			}
			c.report("%s synthesizes a symbol without access to the function (pass b.Func or v) to record the new reference", str(call))
			return true
		})
	}
}

// isPkgFunc reports whether call calls a package-level function.
func (c *checker) isPkgFunc(call *ast.CallExpr) bool {
	var id *ast.Ident
	switch fn := ast.Unparen(call.Fun).(type) {
	case *ast.Ident:
		id = fn
	case *ast.SelectorExpr:
		id = fn.Sel
	default:
		return false
	}
	f, ok := c.res.Info.Uses[id].(*types.Func)
	return ok && f.Type().(*types.Signature).Recv() == nil
}

// isFuncContext reports whether t is *Func, *Block, or *Value.
func isFuncContext(t types.Type) bool {
	p, ok := t.(*types.Pointer)
	if !ok {
		return false
	}
	n, ok := p.Elem().(*types.Named)
	if !ok {
		return false
	}
	switch n.Obj().Name() {
	case "Func", "Block", "Value":
		return true
	}
	return false
}
