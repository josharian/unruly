package typecheck

import (
	"bufio"
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"unicode"

	"github.com/josharian/unruly/rules"
)

// genDecls are declarations harvested from rulegen's generated code.
type genDecls struct {
	imports   []importDecl
	valueType string            // type of v in value rewrite functions, e.g. "*ssa.Value"
	blockType string            // type of b in block rewrite functions
	prelude   map[string]string // b, config, fe, typ -> initializer
}

type importDecl struct{ name, path string }

var (
	valueFuncRx = regexp.MustCompile(`^func [rR]ewriteValue\w*\(v (\*[\w.]+)\) bool`)
	blockFuncRx = regexp.MustCompile(`^func [rR]ewriteBlock\w*\(b (\*[\w.]+)\) bool`)
	preludeRx   = regexp.MustCompile(`^\t(b|config|fe|typ) := (.*)$`)
)

// rulegen's output imports these (when used); rules may use any of them.
var stdImports = []string{
	"fmt", "math", "math/bits", "internal/buildcfg", "cmd/internal/objabi",
	"cmd/internal/obj", "cmd/compile/internal/base", "cmd/compile/internal/types",
	"cmd/compile/internal/ir",
}

func (e *env) generatedDecls(ssaDir, genFile string) (*genDecls, error) {
	d := &genDecls{prelude: make(map[string]string)}
	f, err := parser.ParseFile(token.NewFileSet(), genFile, nil, parser.ImportsOnly)
	if err != nil {
		return nil, err
	}
	have := map[string]bool{}
	for _, spec := range f.Imports {
		path, _ := strconv.Unquote(spec.Path.Value)
		name := filepath.Base(path)
		if spec.Name != nil {
			name = spec.Name.Name
		}
		d.imports = append(d.imports, importDecl{name, path})
		have[name] = true
	}
	for _, path := range stdImports {
		name := filepath.Base(path)
		if !have[name] && exists(filepath.Join(e.root, "src", filepath.FromSlash(path))) {
			d.imports = append(d.imports, importDecl{name, path})
			have[name] = true
		}
	}

	// The prelude declarations appear only in functions that use them,
	// so look through all the generated files, taking the most common
	// initializer for each name.
	files, _ := filepath.Glob(filepath.Join(ssaDir, "rewrite*.go"))
	more, _ := filepath.Glob(filepath.Join(ssaDir, "rewrite", "*", "rewrite*.go"))
	files = append([]string{genFile}, append(files, more...)...)
	counts := map[string]map[string]int{}
	for _, file := range files {
		if err := scanGenerated(file, d, counts); err != nil {
			return nil, err
		}
	}
	for name, m := range counts {
		best := ""
		for init, n := range m {
			if best == "" || n > m[best] || n == m[best] && init < best {
				best = init
			}
		}
		d.prelude[name] = best
	}
	if d.valueType == "" || d.blockType == "" {
		return nil, fmt.Errorf("%s: can't find rewrite function signatures", genFile)
	}
	return d, nil
}

func scanGenerated(file string, d *genDecls, counts map[string]map[string]int) error {
	f, err := os.Open(file)
	if err != nil {
		return err
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	sc.Buffer(nil, 1<<20)
	first := true
	inRewrite := false
	for sc.Scan() {
		b := sc.Bytes()
		if first {
			first = false
			if !bytes.HasPrefix(b, []byte("// Code generated from")) {
				return nil
			}
		}
		if !bytes.HasPrefix(b, []byte("func ")) && !bytes.HasPrefix(b, []byte("\t")) {
			continue
		}
		if bytes.HasPrefix(b, []byte("\t")) && !inRewrite {
			continue
		}
		line := string(b)
		if strings.HasPrefix(line, "func ") {
			inRewrite = false
			if m := valueFuncRx.FindStringSubmatch(line); m != nil {
				inRewrite = true
				if d.valueType == "" {
					d.valueType = m[1]
				}
			} else if m := blockFuncRx.FindStringSubmatch(line); m != nil {
				inRewrite = true
				if d.blockType == "" {
					d.blockType = m[1]
				}
			}
			continue
		}
		if !inRewrite {
			continue
		}
		if m := preludeRx.FindStringSubmatch(line); m != nil {
			if counts[m[1]] == nil {
				counts[m[1]] = map[string]int{}
			}
			counts[m[1]][m[2]]++
		}
	}
	return sc.Err()
}

// Internal fields for rule-level expressions.
const (
	fieldCond Field = 100 + iota
	fieldCode
	fieldPlacement
)

type span struct {
	start, end int // byte offsets of an expression in the generated source
	rule       int
	key        exprKey
}

type generator struct {
	decls *genDecls
	pkg   *types.Package // the rewrite package, for finding conversion functions
	imp   types.Importer

	buf      bytes.Buffer
	rules    []*rules.Rule
	funcs    [][2]int // byte range of each rule's function
	spans    []span
	ruleErrs map[int][]error
	declared map[string]bool
	cur      int
}

func (g *generator) file(pkgName string, set *rules.RuleSet) []byte {
	g.ruleErrs = make(map[int][]error)
	fmt.Fprintf(&g.buf, "package %s\n\nimport (\n", pkgName)
	for _, imp := range g.decls.imports {
		fmt.Fprintf(&g.buf, "\t%s %q\n", imp.name, imp.path)
	}
	g.buf.WriteString(")\n\n")
	for i, r := range set.Rules {
		g.rules = append(g.rules, r)
		g.cur = i
		start := g.buf.Len()
		g.rule(r)
		g.funcs = append(g.funcs, [2]int{start, g.buf.Len()})
	}
	return g.buf.Bytes()
}

func (g *generator) printf(format string, args ...any) { fmt.Fprintf(&g.buf, format, args...) }

// expr writes (text), recording text's span under key.
func (g *generator) expr(text string, node any, f Field) {
	g.buf.WriteString("(")
	g.ident(text, node, f)
	g.buf.WriteString(")")
}

// ident writes text, recording its span under key.
func (g *generator) ident(text string, node any, f Field) {
	// The span must match the parsed expression exactly, which excludes
	// surrounding space, as in the [1<<8 ] of (ORLconst [1<<8 ] x).
	trimmed := strings.TrimLeftFunc(text, unicode.IsSpace)
	g.buf.WriteString(text[:len(text)-len(trimmed)])
	text = strings.TrimRightFunc(trimmed, unicode.IsSpace)
	start := g.buf.Len()
	g.buf.WriteString(text)
	g.spans = append(g.spans, span{start, g.buf.Len(), g.cur, exprKey{node, f}})
	g.buf.WriteString(trimmed[len(text):])
}

func (g *generator) errorf(format string, args ...any) {
	g.ruleErrs[g.cur] = append(g.ruleErrs[g.cur], fmt.Errorf(format, args...))
}

func (g *generator) rule(r *rules.Rule) {
	g.declared = make(map[string]bool)
	if r.IsBlock() {
		g.printf("func _(b %s) {\n", g.decls.blockType)
	} else {
		g.printf("func _(v %s) {\n", g.decls.valueType)
	}
	for _, name := range []string{"b", "config", "fe", "typ"} {
		init, ok := g.decls.prelude[name]
		if !ok || name == "b" && r.IsBlock() {
			continue
		}
		g.printf("%s := %s\n_ = %s\n", name, init, name)
	}
	g.printf("var unrulyR %s\n_ = unrulyR\n", g.decls.valueType)
	// As in rulegen's output, the rule's variables are in an inner scope
	// (there, a for loop), so they may shadow the prelude's names.
	g.printf("{\n")

	if r.IsBlock() {
		mb := r.MatchBlock
		g.matchField(mb, AuxInt, mb.AuxInt, func() string { return g.conv("auxIntTo"+title(mb.Info.AuxIntType)) + "(b.AuxInt)" })
		g.matchField(mb, Aux, mb.Aux, func() string { return g.conv("auxTo"+title(mb.Info.AuxType)) + "(b.Aux)" })
		for i, c := range mb.Controls {
			g.matchValue(c, fmt.Sprintf("b.Controls[%d]", i))
		}
	} else {
		g.matchValue(r.Match, "v")
	}

	if r.Cond != "" {
		g.printf("if ")
		g.expr(r.Cond, r, fieldCond)
		g.printf(" {\n}\n")
	}

	if r.IsBlock() {
		rb := r.ResultBlock
		if rb.AuxInt != "" {
			g.printf("b.AuxInt = %s(", g.conv(unTitle(rb.Info.AuxIntType)+"ToAuxInt"))
			g.expr(rb.AuxInt, rb, AuxInt)
			g.printf(")\n")
		}
		if rb.Aux != "" {
			g.printf("b.Aux = %s(", g.conv(unTitle(rb.Info.AuxType)+"ToAux"))
			g.expr(rb.Aux, rb, Aux)
			g.printf(")\n")
		}
		for _, c := range rb.Controls {
			g.resultNames(c, false, false)
		}
		for _, c := range rb.Controls {
			g.resultValue(c, false, false)
		}
	} else {
		if r.Placement != "" {
			g.printf("b = ")
			g.expr(r.Placement, r, fieldPlacement)
			g.printf("\n")
		}
		if r.ResultCode != "" {
			g.printf("unrulyR = ")
			g.expr(r.ResultCode, r, fieldCode)
			g.printf("\n")
		} else {
			g.resultNames(r.Result, true, r.Placement != "")
			g.resultValue(r.Result, true, r.Placement != "")
		}
	}
	g.printf("}\n}\n\n")
}

// matchValue declares the variables of match node v, whose value is acc,
// as rulegen does, and compares against its non-variable fields.
func (g *generator) matchValue(v *rules.Value, acc string) {
	if v.IsLeaf() {
		if v.Name != "_" {
			g.matchVar(v, acc)
		}
		return
	}
	if v.Name != "" {
		g.matchVar(v, acc)
	}
	g.matchField(v, Type, v.Type, func() string { return acc + ".Type" })
	g.matchField(v, AuxInt, v.AuxInt, func() string { return g.conv("auxIntTo"+title(v.Op.AuxIntType)) + "(" + acc + ".AuxInt)" })
	g.matchField(v, Aux, v.Aux, func() string { return g.conv("auxTo"+title(v.Op.AuxType)) + "(" + acc + ".Aux)" })
	for i, a := range v.Args {
		g.matchValue(a, fmt.Sprintf("%s.Args[%d]", acc, i))
	}
}

// matchVar declares or compares value variable v.Name.
func (g *generator) matchVar(v *rules.Value, acc string) {
	if g.declared[v.Name] {
		g.printf("_ = ")
		g.expr(v.Name, v, Name)
		g.printf(" == %s\n", acc)
		return
	}
	g.declared[v.Name] = true
	g.ident(v.Name, v, Name)
	g.printf(" := %s\n_ = %s\n", acc, v.Name)
}

// matchField declares or compares a <type>, [auxint], or {aux} whose
// value is the Go expression val().
func (g *generator) matchField(node any, f Field, text string, val func() string) {
	if text == "" || text == "_" {
		// rulegen declares _ := ..., then deletes it as unused,
		// making _ a wildcard.
		return
	}
	if rules.IsVarText(text) && !g.declared[text] {
		g.declared[text] = true
		g.ident(text, node, f)
		g.printf(" := %s\n_ = %s\n", val(), text)
		return
	}
	g.printf("_ = %s != ", val())
	g.expr(text, node, f)
	g.printf("\n")
}

// resultNames declares the names of result sub-expressions. In rulegen's
// output, leaves are used only once all their siblings have been created,
// so a leaf may refer to a name declared later in the result.
func (g *generator) resultNames(v *rules.Value, top, placed bool) {
	if v.IsLeaf() {
		return
	}
	if v.Name != "" && (!top || placed) {
		g.ident(v.Name, v, Name)
		g.printf(" := unrulyR\n_ = %s\n", v.Name)
	}
	for _, a := range v.Args {
		g.resultNames(a, false, placed)
	}
}

// resultValue uses the Go expressions of result node v as rulegen does.
func (g *generator) resultValue(v *rules.Value, top, placed bool) {
	if v.IsLeaf() {
		g.printf("unrulyR = ")
		g.expr(v.Name, v, Name)
		g.printf("\n")
		return
	}
	if v.Type != "" {
		g.printf("unrulyR.Type = ")
		g.expr(v.Type, v, Type)
		g.printf("\n")
	}
	if v.AuxInt != "" {
		g.printf("unrulyR.AuxInt = %s(", g.conv(unTitle(v.Op.AuxIntType)+"ToAuxInt"))
		g.expr(v.AuxInt, v, AuxInt)
		g.printf(")\n")
	}
	if v.Aux != "" {
		g.printf("unrulyR.Aux = %s(", g.conv(unTitle(v.Op.AuxType)+"ToAux"))
		g.expr(v.Aux, v, Aux)
		g.printf(")\n")
	}
	for _, a := range v.Args {
		g.resultValue(a, false, placed)
	}
}

// conv returns the expression for rulegen's conversion function name,
// which is in the rewrite package itself (older trees) or exported from
// package ssa (newer trees, which split the rewrite code out).
func (g *generator) conv(name string) string {
	if g.pkg.Scope().Lookup(name) != nil {
		return name
	}
	exported := strings.ToUpper(name[:1]) + name[1:]
	for _, imp := range g.decls.imports {
		if imp.path != "cmd/compile/internal/ssa" {
			continue
		}
		if p, err := g.imp.Import(imp.path); err == nil && p.Scope().Lookup(exported) != nil {
			return imp.name + "." + exported
		}
	}
	g.errorf("no conversion function %s", name)
	return "unrulyMissing_" + name
}

// title and unTitle mirror rulegen's helpers of the same names.
func title(s string) string {
	if i := strings.Index(s, "."); i >= 0 {
		switch strings.ToLower(s[:i]) {
		case "s390x": // keep arch prefix for clarity
			s = s[:i] + s[i+1:]
		default:
			s = s[i+1:]
		}
	}
	if s == "" {
		return s
	}
	return strings.ToUpper(s[:1]) + s[1:]
}

func unTitle(s string) string {
	s = title(s)
	if s == "" {
		return s
	}
	return strings.ToLower(s[:1]) + s[1:]
}

func parseSource(fset *token.FileSet, name string, src []byte) (*ast.File, error) {
	return parser.ParseFile(fset, name, src, parser.SkipObjectResolution)
}

// attach distributes the type-checked expressions and errors to the rules.
func (g *generator) attach(res *Result, f *ast.File, fset *token.FileSet, errs []types.Error) {
	tf := fset.File(f.Pos())
	type offs struct{ start, end int }
	nodes := make(map[offs]ast.Expr)
	ast.Inspect(f, func(n ast.Node) bool {
		if x, ok := n.(ast.Expr); ok {
			k := offs{tf.Offset(x.Pos()), tf.Offset(x.End())}
			if _, dup := nodes[k]; !dup {
				nodes[k] = x
			}
		}
		return true
	})
	trs := make([]*Rule, len(g.rules))
	for i, r := range g.rules {
		trs[i] = &Rule{Vars: make(map[string]*types.Var), exprs: make(map[exprKey]ast.Expr), Errors: g.ruleErrs[i]}
		res.rules[r] = trs[i]
	}
	for _, s := range g.spans {
		x := nodes[offs{s.start, s.end}]
		if x == nil {
			continue
		}
		tr := trs[s.rule]
		switch s.key.field {
		case fieldCond:
			tr.Cond = x
		case fieldCode:
			tr.Code = x
		case fieldPlacement:
			tr.Placement = x
		default:
			tr.exprs[s.key] = x
		}
		if id, ok := x.(*ast.Ident); ok {
			if v, ok := res.Info.Defs[id].(*types.Var); ok {
				tr.Vars[id.Name] = v
			}
		}
	}
	ruleAt := func(pos token.Pos) int {
		if fset.File(pos) != tf {
			return -1
		}
		off := tf.Offset(pos)
		lo, hi := 0, len(g.funcs)
		for lo < hi {
			m := (lo + hi) / 2
			if g.funcs[m][1] <= off {
				lo = m + 1
			} else {
				hi = m
			}
		}
		if lo < len(g.funcs) && g.funcs[lo][0] <= off {
			return lo
		}
		return -1
	}
	for _, terr := range errs {
		if strings.Contains(terr.Msg, "declared and not used") || strings.Contains(terr.Msg, "imported and not used") {
			continue
		}
		if fset.File(terr.Pos) != tf {
			// An artifact of removing function bodies,
			// such as a generic function without a body.
			continue
		}
		i := ruleAt(terr.Pos)
		if i < 0 {
			res.Errors = append(res.Errors, terr)
			continue
		}
		trs[i].Errors = append(trs[i].Errors, fmt.Errorf("%s", terr.Msg))
	}
}
