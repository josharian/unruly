package rulelint

import (
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"path/filepath"
	"regexp"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// sizeUnits reports comparisons of a register value's Type.Size() against
// a bit width. A value in a general-purpose register is at most 8 bytes,
// so x.Type.Size() == 32 is always false, and the rule never fires.
//
// x.Type.Size() <= 16 is always true, which matters only if the rule
// needed its condition. Without knowing the ops' semantics, sizeUnits
// takes a later rule as evidence: one that makes the same rewrite only
// under a condition, as in
//
//	(MOVHZreg (SRWconst [c] x)) && x.Type.Size() <= 16 => (SRWconst [c] x)
//	...
//	(MOVHZreg (SRWconst [c] x)) && c>=16 => (SRWconst [c] x)
//
// Otherwise the condition is dead text but possibly harmless:
// (MOVWZreg (SRWconst [c] x)) && x.Type.Size() <= 32 is correct for every
// x, since srw clears the upper 32 bits.
func (c *checker) sizeUnits() {
	if c.tr.Cond == nil {
		return
	}
	ast.Inspect(c.tr.Cond, func(n ast.Node) bool {
		b, ok := n.(*ast.BinaryExpr)
		if !ok {
			return true
		}
		op := b.Op
		size, k := b.X, b.Y
		if c.constInt(k) < 0 {
			size, k, op = b.Y, b.X, mirror(op)
		}
		bound := c.constInt(k)
		if bound <= 8 {
			return true
		}
		name, ok := sizeOf(size)
		if !ok {
			return true
		}
		v, ok := c.gpValue(name)
		if !ok {
			return true
		}
		// Size() is in [1, 8] and bound > 8.
		prefix := fmt.Sprintf("%s is in bytes and %s is in a general-purpose register (at most 8 bytes), so %s is always",
			str(size), v, str(b))
		switch op {
		case token.GTR, token.GEQ, token.EQL:
			c.report("%s false and the rule never fires; did %d mean bits?", prefix, bound)
		case token.LSS, token.LEQ, token.NEQ:
			if later := c.sameRewriteLater(); later != nil {
				c.report("%s true: the rule rewrites every %s to %s, but the same rewrite at %s:%d holds only when %s (%d looks like a bit width)",
					prefix, c.rule.MatchText, c.rule.ResultText, filepath.Base(later.Pos.File), later.Pos.Line, later.Cond, bound)
			}
		}
		return true
	})
}

// sameRewriteLater returns a later conditional rule for the same op that
// has the same match and result as c.rule, up to renaming of variables,
// or nil.
func (c *checker) sameRewriteLater() *rules.Rule {
	r := c.rule
	if r.IsBlock() {
		return nil
	}
	m, res := canonical(r)
	after := false
	for _, r2 := range r.Set.ByOp[r.Match.Op] {
		if r2 == r {
			after = true
			continue
		}
		if !after || r2.Cond == "" || r2.Pos == r.Pos {
			continue
		}
		if m2, res2 := canonical(r2); m2 == m && res2 == res {
			return r2
		}
	}
	return nil
}

var identRE = regexp.MustCompile(`[A-Za-z_][A-Za-z0-9_]*`)

// canonical returns r's match and result text with match variables
// renamed in order of first appearance in the match.
func canonical(r *rules.Rule) (match, result string) {
	vars := r.MatchVars()
	names := map[string]string{}
	rename := func(s string) string {
		return identRE.ReplaceAllStringFunc(s, func(id string) string {
			if _, ok := vars[id]; !ok {
				return id
			}
			if _, ok := names[id]; !ok {
				names[id] = fmt.Sprintf("v%d", len(names))
			}
			return names[id]
		})
	}
	match = rename(r.MatchText)
	return match, rename(r.ResultText)
}

// constInt returns the value of e if it is a non-negative integer
// constant, or -1.
func (c *checker) constInt(e ast.Expr) int64 {
	v := c.res.Info.Types[e].Value
	if v == nil || v.Kind() != constant.Int {
		return -1
	}
	n, ok := constant.Int64Val(v)
	if !ok || n < 0 {
		return -1
	}
	return n
}

func mirror(op token.Token) token.Token {
	switch op {
	case token.LSS:
		return token.GTR
	case token.LEQ:
		return token.GEQ
	case token.GTR:
		return token.LSS
	case token.GEQ:
		return token.LEQ
	}
	return op
}

// sizeOf matches x.Type.Size() or t.Size() and returns "x.Type" or "t".
func sizeOf(e ast.Expr) (string, bool) {
	call, ok := ast.Unparen(e).(*ast.CallExpr)
	if !ok || len(call.Args) != 0 {
		return "", false
	}
	sel, ok := call.Fun.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Size" {
		return "", false
	}
	switch x := sel.X.(type) {
	case *ast.Ident:
		return x.Name, true
	case *ast.SelectorExpr:
		if id, ok := x.X.(*ast.Ident); ok && x.Sel.Name == "Type" {
			return id.Name + ".Type", true
		}
	}
	return "", false
}

// gpValue reports whether the type named by name (x.Type for value x,
// or t for <t>) belongs to a matched value that is in a general-purpose
// register: the result of an arch op with a GP output, or a GP argument
// of an arch op. It returns a description of the value.
func (c *checker) gpValue(name string) (string, bool) {
	var found string
	var walk func(v, parent *rules.Value, i int)
	walk = func(v, parent *rules.Value, i int) {
		if found != "" {
			return
		}
		isTypeOf := v.Name+".Type" == name || v.Type == name || (parent == nil && name == "v.Type")
		if isTypeOf {
			if v.Op != nil && len(v.Op.Reg.Outputs) == 1 && gpOnly(v.Op.Arch, v.Op.Reg.Outputs[0]) {
				found = v.Name
				if found == "" {
					found = "the " + v.OpName + " result"
				}
				return
			}
			if parent != nil && i < len(parent.Op.Reg.Inputs) && gpOnly(parent.Op.Arch, parent.Op.Reg.Inputs[i]) {
				found = v.Name
				return
			}
		}
		for j, a := range v.Args {
			walk(a, v, j)
		}
	}
	for _, v := range c.rule.MatchValues() {
		walk(v, nil, 0)
	}
	return found, found != ""
}

// gpOnly reports whether m holds only general-purpose registers
// (possibly also SP, SB, and the like).
func gpOnly(a *ops.Arch, m ops.RegMask) bool {
	cl := a.Classify(m)
	return cl&ops.RegGP != 0 && cl&^(ops.RegGP|ops.RegOther) == 0
}
