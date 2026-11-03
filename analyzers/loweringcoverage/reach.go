package loweringcoverage

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// compilerSource is what reachability needs from the compiler's Go source,
// which lives next to the _gen directory.
type compilerSource struct {
	// substitutions are the generic op pairs (from, to) of map literals
	// that SSA passes use to replace one op by another, such as prove's
	// ctzNonZeroOp (Ctz16 => Ctz16NonZero).
	substitutions []substitution
	// intrinsics maps an arch name to its intrinsic registrations.
	intrinsics map[string][]*intrinsicReg
	// unlowered are the generic ops checkLower allows after lowering.
	unlowered map[string]bool
	// general are the ops that ssagen names outside intrinsics, which
	// SSA construction can emit on any arch.
	general map[string]bool
	// overlap maps an arch to the largest size for which
	// isInlinableMemmove turns a memmove whose operands may overlap into
	// a Move.
	overlap map[string]int64
}

type substitution struct {
	from, to string
	where    string // e.g. "prove.go:ctzNonZeroOp"
}

var (
	srcMu    sync.Mutex
	srcCache = map[string]*compilerSource{}
)

// loadSource parses the compiler source of the tree whose _gen directory
// is genDir. It returns nil if the source is not there (as for fixtures).
func loadSource(genDir string) *compilerSource {
	srcMu.Lock()
	defer srcMu.Unlock()
	if s, ok := srcCache[genDir]; ok {
		return s
	}
	s := parseSource(genDir)
	srcCache[genDir] = s
	return s
}

func parseSource(genDir string) *compilerSource {
	internal := filepath.Join(genDir, "..", "..")
	ssagen := filepath.Join(internal, "ssagen")
	if _, err := os.Stat(ssagen); err != nil {
		return nil
	}
	src := &compilerSource{intrinsics: map[string][]*intrinsicReg{}, unlowered: map[string]bool{}, general: map[string]bool{}, overlap: map[string]int64{}}
	// The SSA passes live in package ssa, or in ssacompile in newer trees.
	for _, dir := range []string{filepath.Join(genDir, ".."), filepath.Join(internal, "ssacompile")} {
		for _, f := range parseDir(dir) {
			base := filepath.Base(f.name)
			if base != "rewrite.go" && strings.HasPrefix(base, "rewrite") || base == "opGen.go" {
				// Generated rewrite code and op tables.
				continue
			}
			src.scanPass(f)
		}
	}
	if len(src.unlowered) == 0 {
		return nil
	}
	files := parseDir(ssagen)
	funcs := map[string]*ast.FuncDecl{}
	for _, f := range files {
		for _, d := range f.file.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && fd.Recv == nil {
				funcs[fd.Name.Name] = fd
			}
		}
	}
	for _, f := range files {
		if strings.HasPrefix(filepath.Base(f.name), "simd") {
			continue // generated SIMD intrinsics, lowered by generated SIMD rules
		}
		for _, d := range f.file.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok && registersIntrinsics(fd) {
				src.scanIntrinsics(fd, funcs)
				continue
			}
			ast.Inspect(d, func(n ast.Node) bool {
				if x, ok := n.(ast.Expr); ok {
					if op, ok := opName(x); ok {
						src.general[op] = true
					}
				}
				return true
			})
		}
	}
	return src
}

type parsedFile struct {
	name string
	file *ast.File
}

func parseDir(dir string) []parsedFile {
	names, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	var files []parsedFile
	fset := token.NewFileSet()
	for _, n := range names {
		if strings.HasSuffix(n, "_test.go") {
			continue
		}
		f, err := parser.ParseFile(fset, n, nil, parser.SkipObjectResolution)
		if err != nil {
			continue
		}
		files = append(files, parsedFile{n, f})
	}
	return files
}

// opName returns X for an expression ssa.OpX, ssaop.OpX, or OpX.
func opName(x ast.Expr) (string, bool) {
	var name string
	switch x := x.(type) {
	case *ast.Ident:
		name = x.Name
	case *ast.SelectorExpr:
		if !isPkg(x.X, "ssa") && !isPkg(x.X, "ssaop") {
			return "", false
		}
		name = x.Sel.Name
	default:
		return "", false
	}
	op, ok := strings.CutPrefix(name, "Op")
	return op, ok && op != "" && token.IsExported(op)
}

func (src *compilerSource) scanPass(f parsedFile) {
	ast.Inspect(f.file, func(n ast.Node) bool {
		switch n := n.(type) {
		case *ast.FuncDecl:
			if n.Name.Name == "isInlinableMemmove" {
				src.scanMemmove(n)
			}
			if n.Name.Name == "checkLower" {
				ast.Inspect(n.Body, func(n ast.Node) bool {
					if cc, ok := n.(*ast.CaseClause); ok {
						for _, x := range cc.List {
							if op, ok := opName(x); ok {
								src.unlowered[op] = true
							}
						}
					}
					return true
				})
			}
		case *ast.ValueSpec:
			// var ctzNonZeroOp = map[Op]Op{OpCtz8: OpCtz8NonZero, ...}
			for i, v := range n.Values {
				cl, ok := v.(*ast.CompositeLit)
				if !ok {
					continue
				}
				if _, ok := cl.Type.(*ast.MapType); !ok {
					continue
				}
				for _, e := range cl.Elts {
					kv, ok := e.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					from, ok1 := opName(kv.Key)
					to, ok2 := opName(kv.Value)
					if ok1 && ok2 {
						src.substitutions = append(src.substitutions, substitution{from, to, filepath.Base(f.name) + ":" + n.Names[i].Name})
					}
				}
			}
		}
		return true
	})
}

// goarchs maps GOARCH values to rules arch names.
var goarchs = map[string]string{
	"386": "386", "amd64": "AMD64", "arm": "ARM", "arm64": "ARM64", "loong64": "LOONG64",
	"mips": "MIPS", "mipsle": "MIPS", "mips64": "MIPS64", "mips64le": "MIPS64",
	"ppc64": "PPC64", "ppc64le": "PPC64", "riscv64": "RISCV64", "s390x": "S390X", "wasm": "Wasm",
}

// scanMemmove records, from isInlinableMemmove's switch on the arch,
// the size limit of each case's unconditional disjunct, such as 16 in
//
//	case "amd64":
//		return sz <= 16 || (sz < 1024 && disjoint(dst, sz, src, sz))
func (src *compilerSource) scanMemmove(fd *ast.FuncDecl) {
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		cc, ok := n.(*ast.CaseClause)
		if !ok || len(cc.Body) != 1 {
			return true
		}
		ret, ok := cc.Body[0].(*ast.ReturnStmt)
		if !ok || len(ret.Results) != 1 {
			return true
		}
		limit := int64(-1)
		for _, d := range disjuncts(ret.Results[0]) {
			b, ok := d.(*ast.BinaryExpr)
			if !ok {
				continue
			}
			lit, ok := b.Y.(*ast.BasicLit)
			if !ok || lit.Kind != token.INT {
				continue
			}
			n, err := strconv.ParseInt(lit.Value, 0, 64)
			if err != nil {
				continue
			}
			switch b.Op {
			case token.LEQ:
			case token.LSS:
				n--
			default:
				continue
			}
			limit = max(limit, n)
		}
		for _, x := range cc.List {
			if lit, ok := x.(*ast.BasicLit); ok {
				if a := goarchs[strings.Trim(lit.Value, `"`)]; a != "" && limit >= 0 {
					src.overlap[a] = limit
				}
			}
		}
		return true
	})
}

func disjuncts(x ast.Expr) []ast.Expr {
	switch y := x.(type) {
	case *ast.ParenExpr:
		return disjuncts(y.X)
	case *ast.BinaryExpr:
		if y.Op == token.LOR {
			return append(disjuncts(y.X), disjuncts(y.Y)...)
		}
	}
	return []ast.Expr{x}
}

// archFamilies maps cmd/internal/sys arch families and arches to rules
// arch names (cmd/internal/sys/arch.go).
var archFamilies = map[string]string{
	"AMD64": "AMD64", "I386": "386", "ARM": "ARM", "ARM64": "ARM64", "Loong64": "LOONG64",
	"MIPS": "MIPS", "MIPS64": "MIPS64", "PPC64": "PPC64", "RISCV64": "RISCV64", "S390X": "S390X", "Wasm": "Wasm",
	"ArchAMD64": "AMD64", "Arch386": "386", "ArchARM": "ARM", "ArchARM64": "ARM64", "ArchLoong64": "LOONG64",
	"ArchMIPS": "MIPS", "ArchMIPSLE": "MIPS", "ArchMIPS64": "MIPS64", "ArchMIPS64LE": "MIPS64",
	"ArchPPC64": "PPC64", "ArchPPC64LE": "PPC64", "ArchRISCV64": "RISCV64", "ArchS390X": "S390X", "ArchWasm": "Wasm",
}

// archLists are the arch slices that intrinsic registration passes with
// "...": all arches, those with 4- and 8-byte pointers, and lwatomics,
// all but PPC64 (ssagen/intrinsics.go, initIntrinsics).
var archLists = map[string][]string{
	"all":       {"386", "AMD64", "ARM", "ARM64", "LOONG64", "MIPS", "MIPS64", "PPC64", "RISCV64", "S390X", "Wasm"},
	"p4":        {"386", "ARM", "MIPS"},
	"p8":        {"AMD64", "ARM64", "LOONG64", "MIPS64", "PPC64", "RISCV64", "S390X", "Wasm"},
	"lwatomics": {"386", "AMD64", "ARM", "ARM64", "LOONG64", "MIPS", "MIPS64", "RISCV64", "S390X", "Wasm"},
}

// An intrinsicReg is one add/addF intrinsic registration.
type intrinsicReg struct {
	name    string // e.g. "math/bits.TrailingZeros16"
	builder ast.Expr
	funcs   map[string]*ast.FuncDecl // package-level functions
	locals  map[string]ast.Expr      // local variables of the registering function
}

// registersIntrinsics reports whether fd calls add or addF, the local
// helpers of the function that registers intrinsics (initIntrinsics, or
// InitTables in older trees).
func registersIntrinsics(fd *ast.FuncDecl) bool {
	found := false
	if fd.Body != nil {
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			if c, ok := n.(*ast.CallExpr); ok && isRegistration(c) {
				found = true
			}
			return !found
		})
	}
	return found
}

func isRegistration(c *ast.CallExpr) bool {
	fn, ok := c.Fun.(*ast.Ident)
	return ok && (fn.Name == "add" || fn.Name == "addF") && len(c.Args) >= 4
}

// scanIntrinsics records each add/addF intrinsic registration in fd
// under the arches it registers for.
func (src *compilerSource) scanIntrinsics(fd *ast.FuncDecl, funcs map[string]*ast.FuncDecl) {
	// Local variables holding builders, for registrations that pass them by name.
	locals := map[string]ast.Expr{}
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		if as, ok := n.(*ast.AssignStmt); ok && len(as.Lhs) == len(as.Rhs) {
			for i, l := range as.Lhs {
				if id, ok := l.(*ast.Ident); ok {
					locals[id.Name] = as.Rhs[i]
				}
			}
		}
		return true
	})
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		call, ok := n.(*ast.CallExpr)
		if !ok || !isRegistration(call) {
			return true
		}
		reg := &intrinsicReg{
			name:    strings.Trim(exprString(call.Args[0]), `"`) + "." + strings.Trim(exprString(call.Args[1]), `"`),
			builder: call.Args[2],
			funcs:   funcs,
			locals:  locals,
		}
		for i, a := range call.Args[3:] {
			var arches []string
			if call.Ellipsis.IsValid() && i == len(call.Args)-4 {
				if id, ok := a.(*ast.Ident); ok {
					arches = archLists[id.Name]
				}
			} else if sel, ok := a.(*ast.SelectorExpr); ok && isPkg(sel.X, "sys") {
				if name := archFamilies[sel.Sel.Name]; name != "" {
					arches = []string{name}
				}
			}
			for _, a := range arches {
				src.intrinsics[a] = append(src.intrinsics[a], reg)
			}
		}
		return true
	})
}

// emits returns the ops that reg's builder can emit on an arch with the
// given pointer size, following references to package-level functions
// and to local variables, and skipping if-branches that test the pointer
// size against a different one (as in "if s.config.PtrSize == 4").
func (reg *intrinsicReg) emits(ptrSize int64) map[string]bool {
	ops := map[string]bool{}
	seen := map[string]bool{}
	var collect func(x ast.Node)
	var local func(id *ast.Ident)
	collect = func(x ast.Node) {
		ast.Inspect(x, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.BlockStmt:
				// Stop after an if statement that is known to be
				// taken and returns.
				for _, st := range n.List {
					collect(st)
					if is, ok := st.(*ast.IfStmt); ok && ptrSizeCond(is.Cond, ptrSize) == yes && returns(is.Body) {
						break
					}
				}
				return false
			case *ast.IfStmt:
				if n.Init != nil {
					collect(n.Init)
				}
				switch ptrSizeCond(n.Cond, ptrSize) {
				case yes:
					collect(n.Body)
				case no:
					if n.Else != nil {
						collect(n.Else)
					}
				default:
					collect(n.Cond)
					collect(n.Body)
					if n.Else != nil {
						collect(n.Else)
					}
				}
				return false
			case *ast.SelectorExpr:
				if op, ok := opName(n); ok {
					ops[op] = true
				}
				return false
			case *ast.Ident:
				if op, ok := opName(n); ok {
					ops[op] = true
				}
				if seen[n.Name] {
					return false
				}
				if fd := reg.funcs[n.Name]; fd != nil && fd.Body != nil {
					seen[n.Name] = true
					collect(fd.Body)
				}
			case *ast.CallExpr:
				if id, ok := n.Fun.(*ast.Ident); ok {
					local(id)
				}
			}
			return true
		})
	}
	// Follow local variables only where they are called or are the
	// builder itself: closures reuse names like v for unrelated values.
	local = func(id *ast.Ident) {
		if rhs := reg.locals[id.Name]; rhs != nil && !seen[id.Name] && reg.funcs[id.Name] == nil {
			seen[id.Name] = true
			collect(rhs)
		}
	}
	if id, ok := reg.builder.(*ast.Ident); ok {
		local(id)
	}
	collect(reg.builder)
	return ops
}

func returns(b *ast.BlockStmt) bool {
	if len(b.List) == 0 {
		return false
	}
	_, ok := b.List[len(b.List)-1].(*ast.ReturnStmt)
	return ok
}

// ptrSizeCond evaluates conditions of the form X.PtrSize == N (or !=,
// or RegSize, which equals PtrSize on every arch but amd64p32, long gone).
func ptrSizeCond(x ast.Expr, ptrSize int64) tri {
	b, ok := x.(*ast.BinaryExpr)
	if !ok || b.Op != token.EQL && b.Op != token.NEQ {
		return maybe
	}
	sel, ok := b.X.(*ast.SelectorExpr)
	if !ok || sel.Sel.Name != "PtrSize" && sel.Sel.Name != "RegSize" {
		return maybe
	}
	lit, ok := b.Y.(*ast.BasicLit)
	if !ok || lit.Kind != token.INT {
		return maybe
	}
	eq := lit.Value == fmt.Sprint(ptrSize)
	return triOf(eq == (b.Op == token.EQL))
}

func exprString(x ast.Expr) string {
	if bl, ok := x.(*ast.BasicLit); ok {
		return bl.Value
	}
	return "?"
}

// checkReach reports generic ops that can reach set's lower pass but have
// no lowering rule.
func checkReach(pass *analysis.Pass, ai *archInfo, set *rules.RuleSet) {
	src := loadSource(pass.Ops.Dir)
	if src == nil {
		return
	}
	// Intrinsics describe the tree the op tables came from; they say
	// nothing about rules from elsewhere, such as test fixtures.
	checkIntrinsics := sameTree(set, pass.Ops.Dir)
	g := pass.Ops.Generic
	// An op is lowered if some rule matches it, at the root or (as for
	// tuple ops like Add64carry, lowered via Select0 and Select1) inside.
	matched := map[*ops.Op]bool{}
	for _, r := range set.Rules {
		for _, mv := range r.MatchValues() {
			mv.Walk(func(v *rules.Value) bool {
				if v.Op != nil {
					matched[v.Op] = true
				}
				return true
			})
		}
	}
	lowered := func(name string) bool {
		op := g.Op(name)
		return op == nil || matched[op] || src.unlowered[name] ||
			handledBeforeLower(pass.Corpus, ai, op)
	}

	emitted := map[string]string{} // op => intrinsic
	for _, reg := range src.intrinsics[set.Arch.Name] {
		for op := range reg.emits(ai.ptrSize) {
			if _, ok := emitted[op]; !ok {
				emitted[op] = reg.name
			}
		}
	}
	// reachable reports whether op can reach lowering on this arch.
	// For rules from elsewhere (fixtures), a lowering rule for op is
	// taken as evidence that it can.
	reachable := func(op *ops.Op) bool {
		if !checkIntrinsics || len(src.general) == 0 {
			return len(set.ByOp[op]) > 0
		}
		_, ok := emitted[op.Name]
		return ok || src.general[op.Name] || producedByRules(pass.Corpus, set, op)
	}

	reported := map[string]bool{}
	for _, s := range src.substitutions {
		from := g.Op(s.from)
		if from == nil || len(set.ByOp[from]) == 0 || !reachable(from) || lowered(s.to) || reported[s.to] {
			continue
		}
		reported[s.to] = true
		pass.Reportf(set.ByOp[from][0].Pos, "%s lowers %s, which %s replaces by %s, but has no rule for %s; it would reach codegen unlowered (\"not lowered\" compiler crash)",
			set.Arch.Name, s.from, s.where, s.to, s.to)
	}

	if !checkIntrinsics {
		return
	}
	var names []string
	for op := range emitted {
		names = append(names, op)
	}
	sort.Strings(names)
	for _, name := range names {
		op := g.Op(name)
		if op == nil || op.SIMD || lowered(name) || reported[name] {
			continue
		}
		reported[name] = true
		p := firstPos(set)
		if sib := sibling(set, name); sib != nil {
			p = sib.Pos
		}
		pass.Reportf(p, "intrinsic %s on %s emits %s, but %s has no rule lowering %s; it would reach codegen unlowered (\"not lowered\" compiler crash)",
			emitted[name], set.Arch.Name, name, set.Arch.Name, name)
	}
}

// producedByRules reports whether a rule of a generic rule set, or of
// set itself, can produce op.
func producedByRules(c *rules.Corpus, set *rules.RuleSet, op *ops.Op) bool {
	for _, s := range c.Sets {
		if s != set && !(s.Arch.Generic && s.Suffix == "") {
			continue
		}
		for _, r := range s.Rules {
			found := false
			for _, rv := range r.ResultValues() {
				rv.Walk(func(v *rules.Value) bool {
					found = found || v.Op == op
					return !found
				})
			}
			if found {
				return true
			}
		}
	}
	return false
}

// decomposedKinds are the operand kinds whose values the "decompose
// builtin" and "decompose user" passes split into scalars before
// lowering (ssacompile/decompose.go), taking the ops that make and take
// them apart with them.
var decomposedKinds = map[opsig.Kind]bool{
	opsig.String: true, opsig.Slice: true, opsig.Interface: true,
	opsig.Complex: true, opsig.Struct: true, opsig.Array: true,
}

// handledBeforeLower reports whether op is gone before the lower pass on
// ai's arch: a decomposition op, an op that dec64 handles on a 32-bit
// arch, or an op that a generic rule set rewrites away unconditionally.
func handledBeforeLower(c *rules.Corpus, ai *archInfo, op *ops.Op) bool {
	if sig, ok := opsig.Lookup(op); ok {
		operands := append([]opsig.Operand{sig.Result}, sig.Args...)
		for _, o := range operands {
			if decomposedKinds[o.Kind] {
				return true
			}
		}
	}
	switch op.Name {
	case "Int64Make", "Int64Hi", "Int64Lo":
		if ai.ptrSize == 4 {
			return true
		}
	}
	for _, s := range c.Sets {
		if !s.Arch.Generic || s.Suffix != "" {
			continue
		}
		if s.Arch.Name == "dec64" {
			if ai.ptrSize == 4 && len(s.ByOp[op]) > 0 {
				return true
			}
			continue
		}
		for _, r := range s.ByOp[op] {
			if r.Unconditional() {
				return true
			}
		}
	}
	return false
}

// sibling returns the first lowering rule for an op whose name shares the
// longest prefix with name, as a place to report a missing lowering.
func sibling(set *rules.RuleSet, name string) *rules.Rule {
	var best *rules.Rule
	bestLen := 2
	for op, rs := range set.ByOp {
		if !op.IsGeneric() || len(rs) == 0 {
			continue
		}
		n := commonPrefix(op.Name, name)
		if n > bestLen || n == bestLen && best != nil && rs[0].Pos.Line < best.Pos.Line {
			best, bestLen = rs[0], n
		}
	}
	return best
}

func commonPrefix(a, b string) int {
	n := 0
	for n < len(a) && n < len(b) && a[n] == b[n] {
		n++
	}
	return n
}

func firstPos(set *rules.RuleSet) rules.Pos {
	if len(set.Rules) == 0 {
		return rules.Pos{}
	}
	return set.Rules[0].Pos
}

// intrinsicsAnywhere makes checkReach consult intrinsics even for rules
// that are not from the op tables' tree. Tests set it.
var intrinsicsAnywhere = false

func sameTree(set *rules.RuleSet, genDir string) bool {
	if intrinsicsAnywhere {
		return true
	}
	if len(set.Files) == 0 {
		return false
	}
	a, err1 := filepath.Abs(filepath.Dir(set.Files[0].Path))
	b, err2 := filepath.Abs(genDir)
	return err1 == nil && err2 == nil && a == b
}
