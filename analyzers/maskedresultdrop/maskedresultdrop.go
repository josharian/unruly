// Package maskedresultdrop reports rules that simplify a masked x86 SIMD
// op to a value that ignores the mask.
package maskedresultdrop

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "maskedresultdrop",
	Doc: `report rules that rewrite a masked x86 SIMD op to a result that ignores its mask

An AVX-512 op with a K-register mask writes only the lanes the mask
selects. A zeroing op (emitted with the .Z suffix) sets the other lanes to
zero; a merging op (ResultInArg0, such as VPADDDMasked512Merging dst x y k)
leaves them as they were in dst. Either way, the value depends on the mask,
so a simplification of the op must keep it. For example,

	(VPSLLWMasked128const [a] x mask) && a==0 => x

is wrong: with a == 0 the op computes mask ? x : 0 lane by lane, and the
rule drops the zeroing. The result should be (VMOVDQU16Masked128 x mask).

Zeroing ops are those that the arch's codegen (<arch>/ssa.go and
<arch>/simdssa.go) emits with x86.ParseSuffix(p, "Z"). A rule is reported
if its match is rooted at a zeroing or merging op and its result mentions
none of the variables bound in the mask argument.`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	cache := map[*ops.Arch]map[string]bool{}
	for r := range pass.Rules() {
		if r.IsBlock() || r.Match.Op == nil || r.Match.Op.IsGeneric() {
			continue
		}
		op := r.Match.Op
		a := op.Arch
		zero, ok := cache[a]
		if !ok {
			var err error
			zero, err = zeroingOps(pass.Ops.Dir, a.Name)
			if err != nil {
				return err
			}
			cache[a] = zero
		}
		if len(zero) == 0 {
			// Not an arch with x86-style zeroing and merging masks.
			continue
		}
		mi := maskArg(op)
		if mi < 0 || mi >= len(r.Match.Args) {
			continue
		}
		var kind string
		switch {
		case zero[op.Name]:
			kind = "zeroing"
		case op.ResultInArg0:
			kind = "merging"
		default:
			continue
		}
		if r.Result == nil {
			continue // {code} result; can't tell
		}
		vars := map[string]bool{}
		r.Match.Args[mi].Walk(func(v *rules.Value) bool {
			if v.IsVar() {
				vars[v.Name] = true
			}
			if v.Name != "" && !v.IsLeaf() {
				vars[v.Name] = true
			}
			return true
		})
		if mentions(r.Result, vars) {
			continue
		}
		pass.Reportf(r.Pos, "%s", describe(r, kind, mi))
	}
	return nil
}

func describe(r *rules.Rule, kind string, mi int) string {
	op := r.Match.Op
	mask := r.Match.Args[mi].Text
	res := "result " + r.Result.Text + " does not use it"
	if r.Result.IsLeaf() {
		res = "result " + r.Result.Text + " keeps every lane"
	}
	if kind == "zeroing" {
		return fmt.Sprintf("mask dropped: %s zeroes the lanes where %s is false, but the %s (keep the mask, e.g. with a VMOVDQU<E>Masked wrapper)", op.Name, mask, res)
	}
	return fmt.Sprintf("mask dropped: %s keeps dst %s in the lanes where %s is false, but the %s", op.Name, r.Match.Args[0].Text, mask, res)
}

// mentions reports whether any of vars occurs in v, as a leaf variable,
// a binding name, or an identifier in a leaf Go expression or in an
// aux or auxint expression.
func mentions(v *rules.Value, vars map[string]bool) bool {
	found := false
	v.Walk(func(w *rules.Value) bool {
		if found {
			return false
		}
		for _, s := range []string{w.Type, w.AuxInt, w.Aux} {
			if s != "" && exprMentions(s, vars) {
				found = true
			}
		}
		if w.IsLeaf() && exprMentions(w.Name, vars) {
			found = true
		}
		return !found
	})
	return found
}

func exprMentions(s string, vars map[string]bool) bool {
	e, err := parser.ParseExpr(s)
	if err != nil {
		return vars[s]
	}
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		if id, ok := n.(*ast.Ident); ok && vars[id.Name] {
			found = true
		}
		return !found
	})
	return found
}

// maskArg returns the index of op's mask-register (AVX-512 K register)
// argument, or -1.
func maskArg(op *ops.Op) int {
	k := maskRegs(op.Arch)
	for i, in := range op.Reg.Inputs {
		if !in.Empty() && !k.Empty() && in.Minus(k).Empty() {
			return i
		}
	}
	return -1
}

// maskRegs returns a's SIMD mask registers. Trees before the
// simdmaskreg arch field (October 2026) don't declare them; there, they
// are the registers named K0-K7.
func maskRegs(a *ops.Arch) ops.RegMask {
	if !a.SIMDMaskRegs.Empty() {
		return a.SIMDMaskRegs
	}
	var m ops.RegMask
	for i, name := range a.RegNames {
		if len(name) == 2 && name[0] == 'K' && '0' <= name[1] && name[1] <= '7' {
			m = m.Add(i)
		}
	}
	return m
}

// zeroingOps returns the ops of arch whose codegen applies the "Z"
// (zeroing-masking) suffix: the op names in each case clause of the
// arch's codegen package (cmd/compile/internal/<arch>) whose body calls
// x86.ParseSuffix(p, "Z"). It returns an empty set if there are none or
// the codegen package is missing.
func zeroingOps(genDir, arch string) (map[string]bool, error) {
	dir := filepath.Join(genDir, "..", "..", strings.ToLower(arch))
	paths, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	set := map[string]bool{}
	fset := token.NewFileSet()
	prefix := "Op" + arch
	for _, p := range paths {
		if strings.HasSuffix(p, "_test.go") {
			continue
		}
		src, err := os.ReadFile(p)
		if err != nil {
			return nil, err
		}
		if !strings.Contains(string(src), `"Z"`) {
			continue
		}
		f, err := parser.ParseFile(fset, p, src, 0)
		if err != nil {
			return nil, err
		}
		ast.Inspect(f, func(n ast.Node) bool {
			cc, ok := n.(*ast.CaseClause)
			if !ok || !callsZeroSuffix(cc.Body) {
				return true
			}
			for _, e := range cc.List {
				if sel, ok := e.(*ast.SelectorExpr); ok && strings.HasPrefix(sel.Sel.Name, prefix) {
					set[strings.TrimPrefix(sel.Sel.Name, prefix)] = true
				}
			}
			return true
		})
	}
	return set, nil
}

func callsZeroSuffix(body []ast.Stmt) bool {
	found := false
	for _, s := range body {
		ast.Inspect(s, func(n ast.Node) bool {
			call, ok := n.(*ast.CallExpr)
			if !ok || len(call.Args) != 2 {
				return true
			}
			sel, ok := call.Fun.(*ast.SelectorExpr)
			if !ok || sel.Sel.Name != "ParseSuffix" {
				return true
			}
			if lit, ok := call.Args[1].(*ast.BasicLit); ok {
				if v, err := strconv.Unquote(lit.Value); err == nil && v == "Z" {
					found = true
				}
			}
			return true
		})
	}
	return found
}
