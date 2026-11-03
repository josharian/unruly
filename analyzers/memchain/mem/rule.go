package mem

import (
	"go/ast"
	"go/parser"
	"go/token"
	"strconv"
	"unicode"
	"unicode/utf8"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// Rule is a value rule annotated with memory facts.
type Rule struct {
	*rules.Rule
	T *Table

	// Parent maps each match node to its parent in the match tree.
	Parent map[*rules.Value]*rules.Value
	// Bind maps each match variable that names a value to the node that
	// binds it: its first occurrence, a compound node or a leaf.
	Bind map[string]*rules.Value
	// MemVars are the match variables that are memory states.
	MemVars map[string]bool

	Cond *Cond
}

// Analyze annotates r, which must be a value rule.
func Analyze(t *Table, r *rules.Rule) *Rule {
	mr := &Rule{
		Rule:   r,
		T:      t,
		Parent: make(map[*rules.Value]*rules.Value),
		Bind:   make(map[string]*rules.Value),
	}
	var walk func(v *rules.Value)
	walk = func(v *rules.Value) {
		if rules.IsVarText(v.Name) && mr.Bind[v.Name] == nil {
			mr.Bind[v.Name] = v
		}
		for _, a := range v.Args {
			mr.Parent[a] = v
			walk(a)
		}
	}
	walk(r.Match)
	mr.MemVars = memVars(func(op *ops.Op) *OpInfo { i := t.Op(op); return &i }, r)
	mr.Cond = ParseCond(r.CondExpr)
	return mr
}

// Info returns the classification of v's op.
func (r *Rule) Info(v *rules.Value) OpInfo {
	if v == nil || v.IsLeaf() {
		return OpInfo{Out: OutNone}
	}
	return r.T.Op(v.Op)
}

// MemArg returns v's memory argument, or nil.
func (r *Rule) MemArg(v *rules.Value) *rules.Value {
	if v.IsLeaf() || len(v.Args) == 0 || v.Rest || !r.Info(v).Mem {
		return nil
	}
	return v.Args[len(v.Args)-1]
}

// Refs returns the number of argument positions in the match that hold
// the value named name or one of its aliases (see Cond.Alias). This is
// the use count the value must have for the match to account for all of
// its uses; the root, which has no position, counts 0.
func (r *Rule) Refs(name string) int {
	n := 0
	r.Match.Walk(func(v *rules.Value) bool {
		if v != r.Match && v.Name != "" && r.Cond.SameValue(v.Name, name) {
			n++
		}
		return true
	})
	return n
}

// Dies reports whether the condition proves that the value named name
// has no uses outside the match: name.Uses == k for k at most its Refs,
// or CanMergeLoad(v, name) or CanMergeLoadClobber(v, name, _), which
// check name.Uses == 1.
func (r *Rule) Dies(name string) bool {
	if r.Cond.MergeLoad[name] {
		return true
	}
	refs := r.Refs(name)
	for n, k := range r.Cond.Uses {
		if r.Cond.SameValue(n, name) && k <= refs {
			return true
		}
	}
	return false
}

// Cond holds facts established by a rule condition's top-level
// conjuncts. Facts under || or ! are not included.
type Cond struct {
	Conjuncts []ast.Expr
	// Uses maps x to k for each conjunct x.Uses == k.
	Uses map[string]int
	// MergeLoad holds x for CanMergeLoad(v, x) and CanMergeLoadClobber(v, x, _).
	MergeLoad map[string]bool
	// Clobber holds the arguments of Clobber calls.
	Clobber map[string]bool
	// ResetCopy holds x for resetCopy(x, _), which turns x into a copy.
	ResetCopy map[string]bool
	// Calls are the conjuncts that are calls, by Fn name.
	Calls map[string][]*ast.CallExpr
	// NotCalls are the conjuncts !f(...), by Fn name.
	NotCalls map[string][]*ast.CallExpr

	alias map[string]string // union-find over x == y conjuncts
}

// ParseCond extracts the facts of cond, which may be nil.
func ParseCond(cond ast.Expr) *Cond {
	c := &Cond{
		Uses:      make(map[string]int),
		MergeLoad: make(map[string]bool),
		Clobber:   make(map[string]bool),
		ResetCopy: make(map[string]bool),
		Calls:     make(map[string][]*ast.CallExpr),
		NotCalls:  make(map[string][]*ast.CallExpr),
		alias:     make(map[string]string),
	}
	var split func(e ast.Expr)
	split = func(e ast.Expr) {
		e = ast.Unparen(e)
		if b, ok := e.(*ast.BinaryExpr); ok && b.Op == token.LAND {
			split(b.X)
			split(b.Y)
			return
		}
		c.Conjuncts = append(c.Conjuncts, e)
	}
	if cond != nil {
		split(cond)
	}
	for _, e := range c.Conjuncts {
		switch e := e.(type) {
		case *ast.BinaryExpr:
			if e.Op != token.EQL {
				break
			}
			x, y := ast.Unparen(e.X), ast.Unparen(e.Y)
			if n, k, ok := usesEq(x, y); ok {
				c.Uses[n] = k
			} else if n, k, ok := usesEq(y, x); ok {
				c.Uses[n] = k
			} else if a, ok := x.(*ast.Ident); ok {
				if b, ok := y.(*ast.Ident); ok {
					c.union(a.Name, b.Name)
				}
			}
		case *ast.CallExpr:
			fn := Fn(e)
			c.Calls[fn] = append(c.Calls[fn], e)
			switch fn {
			case "canMergeLoad", "canMergeLoadClobber":
				if len(e.Args) >= 2 {
					if id, ok := e.Args[1].(*ast.Ident); ok {
						c.MergeLoad[id.Name] = true
					}
				}
			case "clobber":
				for _, a := range e.Args {
					if id, ok := a.(*ast.Ident); ok {
						c.Clobber[id.Name] = true
					}
				}
			case "resetCopy":
				if len(e.Args) >= 1 {
					if id, ok := e.Args[0].(*ast.Ident); ok {
						c.ResetCopy[id.Name] = true
					}
				}
			}
		case *ast.UnaryExpr:
			if call, ok := ast.Unparen(e.X).(*ast.CallExpr); ok && e.Op == token.NOT {
				fn := Fn(call)
				c.NotCalls[fn] = append(c.NotCalls[fn], call)
			}
		}
	}
	return c
}

// usesEq reports whether x is name.Uses and y is an integer literal.
func usesEq(x, y ast.Expr) (string, int, bool) {
	sel, ok := x.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "Uses" {
		return "", 0, false
	}
	id, ok := sel.X.(*ast.Ident)
	if !ok {
		return "", 0, false
	}
	lit, ok := y.(*ast.BasicLit)
	if !ok || lit.Kind != token.INT {
		return "", 0, false
	}
	k, err := strconv.Atoi(lit.Value)
	if err != nil {
		return "", 0, false
	}
	return id.Name, k, true
}

func (c *Cond) find(x string) string {
	for {
		p, ok := c.alias[x]
		if !ok || p == x {
			return x
		}
		x = p
	}
}

func (c *Cond) union(a, b string) {
	ra, rb := c.find(a), c.find(b)
	if ra != rb {
		c.alias[ra] = rb
	}
}

// SameValue reports whether a and b name the same value, because they
// are the same name or the condition asserts a == b.
func (c *Cond) SameValue(a, b string) bool { return a == b || c.find(a) == c.find(b) }

// Fn returns the normalized name of the function call calls: without
// any package qualifier and with its first letter lowercased, so that
// ssa.Clobber (in current trees) and clobber (in older ones) are both
// "clobber".
func Fn(call *ast.CallExpr) string {
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

// Idents returns the identifiers in the Go expression src, or nil if it
// does not parse. Selector names (the Uses in x.Uses) are not included.
func Idents(src string) map[string]bool {
	if src == "" {
		return nil
	}
	e, err := parser.ParseExpr(src)
	if err != nil {
		return nil
	}
	ids := make(map[string]bool)
	ast.Inspect(e, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.SelectorExpr:
			ast.Inspect(n.X, func(m ast.Node) bool {
				if id, ok := m.(*ast.Ident); ok {
					ids[id.Name] = true
				}
				return true
			})
			return false
		case *ast.Ident:
			ids[n.Name] = true
		}
		return true
	})
	return ids
}

// Mentions reports whether any expression in the result tree v (its
// leaves, types, auxints, and auxes) mentions the identifier name.
func Mentions(v *rules.Value, name string) bool {
	found := false
	v.Walk(func(w *rules.Value) bool {
		if found {
			return false
		}
		if w.IsLeaf() {
			found = Idents(w.Name)[name]
			return false
		}
		for _, s := range []string{w.Type, w.AuxInt, w.Aux} {
			if Idents(s)[name] {
				found = true
			}
		}
		return !found
	})
	return found
}

// ArgIdents returns the identifiers in a call's argument i, or nil.
func ArgIdents(call *ast.CallExpr, i int) map[string]bool {
	if i >= len(call.Args) {
		return nil
	}
	ids := make(map[string]bool)
	ast.Inspect(call.Args[i], func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok {
			ids[id.Name] = true
		}
		return true
	})
	return ids
}

// ArgIdent returns call's argument i if it is a plain identifier, or "".
func ArgIdent(call *ast.CallExpr, i int) string {
	if i >= len(call.Args) {
		return ""
	}
	if id, ok := ast.Unparen(call.Args[i]).(*ast.Ident); ok {
		return id.Name
	}
	return ""
}
