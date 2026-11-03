package condsem

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// arch is the semantic model of one architecture's flags, condition codes,
// and the ops that produce and consume them.
type arch struct {
	name    string
	ptrW    uint8
	ops     map[string]*opSem
	blocks  map[string]*blockSem
	conds   []*cond // the conditions consumers can test, for comparing flags
	compute func(f *flags)

	// ccOps are the ops that name conditions in aux fields (ARM64 CSEL).
	ccOps     map[string]*cond
	ccOpNames []string

	// invOrigins are the kinds of flags the arch's rules wrap in
	// InvertFlags. Only those are enumerated beneath InvertFlags.
	invOrigins map[origin]bool
	producers  []producer
	consts     []*flags // the flag constants, also enumerated for flags variables
	domains    map[[2]int][]*flags
}

// producer is a kind of flags value to enumerate for flags variables.
type producer struct {
	op     string
	o      origin
	w      uint8
	signed bool // PPC64
}

func (a *arch) sem(op *ops.Op) *opSem {
	var s *opSem
	if op.IsGeneric() {
		s = genericOps[op.Name]
	} else {
		s = a.ops[op.Name]
	}
	if s == nil {
		unmodeled("op %s", op.Name)
	}
	return s
}

func (a *arch) blockSem(b *ops.Block) *blockSem {
	var s *blockSem
	if b.IsGeneric() {
		s = genericBlocks[b.Name]
	} else {
		s = a.blocks[b.Name]
	}
	if s == nil {
		unmodeled("block %s", b.Name)
	}
	return s
}

func (a *arch) invertible(f *flags) bool {
	return f.o == oConst || a.invOrigins[f.o]
}

// newFlags returns the flags produced by op.
func (a *arch) newFlags(op string, o origin, x, y uint64, w uint8) *flags {
	f := &flags{op: op, o: o, a: trunc(x, w), b: trunc(y, w), w: w}
	a.compute(f)
	return f
}

func (a *arch) newFloatFlags(op string, x, y float64) *flags {
	f := &flags{op: op, o: oFloat, fa: x, fb: y}
	a.compute(f)
	return f
}

// invert returns InvertFlags(f): the flags of the comparison with its
// operands swapped.
func (a *arch) invert(f *flags) *flags {
	g := *f
	g.op = f.op
	g.a, g.b = f.b, f.a
	g.fa, g.fb = f.fb, f.fa
	g.known, g.stale, g.set = 0, 0, 0
	g.inner = nil
	switch f.o {
	case oSub, oFloat:
		a.compute(&g)
	case oConst:
		g = *invertConst(f)
	default:
		unmodeled("InvertFlags of %s", f.op)
	}
	return &flags{op: "InvertFlags", o: g.o, a: g.a, b: g.b, w: g.w, fa: g.fa, fb: g.fb,
		signed: g.signed, aux: g.aux, inner: f, known: g.known, stale: g.stale, set: g.set}
}

// invertConst inverts a constant recording a relation between operands.
func invertConst(f *flags) *flags {
	g := &flags{op: f.op, o: oConst}
	// x86-style constants record Z, C (unsigned less), and N^V (signed less).
	// PPC64-style constants record LT, GT, EQ.
	get := func(b bit) (bool, bool) {
		t := f.get(b)
		return t == tTrue, t.known()
	}
	z, zk := get(bZ)
	lt, ltk := get(bLT)
	gt, gtk := get(bGT)
	if ltk && gtk {
		eq, _ := get(bEQ)
		g.setBit(bLT, gt)
		g.setBit(bGT, lt)
		g.setBit(bEQ, eq)
		return g
	}
	slt, sk := get(bNxV)
	ult, uk := get(bC)
	if !zk || !sk || !uk || f.known&(1<<bN|1<<bV) != 0 {
		unmodeled("InvertFlags of %s", f.op)
	}
	g.setBit(bZ, z)
	g.setBit(bNxV, !slt && !z)
	g.setBit(bC, !ult && !z)
	return g
}

// flagDomain returns the flags values to try for a flags variable.
func (a *arch) flagDomain(cat fcat, inv bool) []*flags {
	key := [2]int{int(cat), 0}
	if inv {
		key[1] = 1
	}
	if d, ok := a.domains[key]; ok {
		return d
	}
	var gens [][]*flags
	for _, p := range a.producers {
		if p.o == oFloat && cat&catFloat == 0 || p.o != oFloat && cat&catInt == 0 {
			continue
		}
		if inv && !a.invOrigins[p.o] {
			continue
		}
		var g []*flags
		switch p.o {
		case oSub, oAdd:
			for _, xy := range pairs(len(flagOperands)) {
				f := &flags{op: p.op, o: p.o, a: trunc(flagOperands[xy[0]], p.w), b: trunc(flagOperands[xy[1]], p.w), w: p.w, signed: p.signed}
				a.compute(f)
				g = append(g, f)
			}
		case oLogic:
			for _, x := range intDomain[:16] {
				g = append(g, a.newFlags(p.op, p.o, x, 0, p.w))
			}
		case oFloat:
			fd := floatDomain[:6]
			for _, xy := range pairs(len(fd)) {
				g = append(g, a.newFloatFlags(p.op, fd[xy[0]], fd[xy[1]]))
			}
		}
		gens = append(gens, g)
	}
	if !inv && cat&catInt != 0 {
		gens = append(gens, a.consts)
	}
	// Interleave, so that every prefix has variety.
	var d []*flags
	for i := 0; ; i++ {
		more := false
		for _, g := range gens {
			if i < len(g) {
				d = append(d, g[i])
				more = true
			}
		}
		if !more {
			break
		}
	}
	if a.domains == nil {
		a.domains = make(map[[2]int][]*flags)
	}
	a.domains[key] = d
	return d
}

// pairs returns the pairs of indexes less than n, by increasing sum.
func pairs(n int) [][2]int {
	var p [][2]int
	for s := 0; s <= 2*(n-1); s++ {
		for i := 0; i < n; i++ {
			if j := s - i; j >= 0 && j < n {
				p = append(p, [2]int{i, j})
			}
		}
	}
	return p
}

// findInverted records which kinds of flags the rule set wraps in
// InvertFlags.
func (a *arch) findInverted(set *rules.RuleSet) {
	if a.invOrigins == nil {
		a.invOrigins = make(map[origin]bool)
	}
	found := false
	for _, r := range set.Rules {
		for _, v := range r.ResultValues() {
			v.Walk(func(v *rules.Value) bool {
				if v.Op != nil && v.Op.Name == "InvertFlags" && len(v.Args) == 1 && v.Args[0].Op != nil {
					if s := a.ops[v.Args[0].Op.Name]; s != nil && s.origin != oConst {
						a.invOrigins[s.origin] = true
						found = true
					}
				}
				return true
			})
		}
	}
	if !found && set.Suffix == "" {
		// A main rule set without canonicalization rules (a test
		// fixture): any compare may be inverted.
		a.invOrigins[oSub] = true
		a.invOrigins[oFloat] = true
	}
}

// codegenTables holds tables parsed from an arch's ssa.go, which defines
// what each block kind and condition op means in machine terms.
type codegenTables struct {
	// blockJump maps a block kind to the branch taken to its first
	// successor, as a condition name such as "EQ" or "HI".
	blockJump map[string]string
	// blockEq lists PPC64 block kinds that also branch to the first
	// successor on EQ (blockJump's asmeq field).
	blockEq map[string]bool
	// condBits maps a condition op to its condition name.
	condBits map[string]string
}

// parseCodegen parses the codegen tables of the arch's ssa.go, which the
// arch's Raw "genfile" names relative to the _gen directory.
func parseCodegen(a *ops.Arch) *codegenTables {
	t := &codegenTables{blockJump: map[string]string{}, blockEq: map[string]bool{}, condBits: map[string]string{}}
	gf, _ := a.Raw["genfile"].(string)
	if gf == "" {
		return t
	}
	path := filepath.Join(a.Tables().Dir, filepath.FromSlash(gf))
	src, err := os.ReadFile(path)
	if err != nil {
		return t
	}
	f, err := parser.ParseFile(token.NewFileSet(), path, src, 0)
	if err != nil {
		return t
	}
	name := func(e ast.Expr) string {
		if s, ok := e.(*ast.SelectorExpr); ok {
			return s.Sel.Name
		}
		if id, ok := e.(*ast.Ident); ok {
			return id.Name
		}
		return ""
	}
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.VAR {
			continue
		}
		for _, s := range g.Specs {
			vs := s.(*ast.ValueSpec)
			if len(vs.Names) != 1 || len(vs.Values) != 1 {
				continue
			}
			lit, ok := vs.Values[0].(*ast.CompositeLit)
			if !ok {
				continue
			}
			switch vs.Names[0].Name {
			case "blockJump":
				for _, e := range lit.Elts {
					kv, ok := e.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					k := strings.TrimPrefix(strings.TrimPrefix(name(kv.Key), "Block"), a.Name)
					v, ok := kv.Value.(*ast.CompositeLit)
					if !ok || len(v.Elts) < 2 {
						continue
					}
					asm := name(v.Elts[0])
					asm = strings.TrimPrefix(asm, "AJ") // x86
					asm = strings.TrimPrefix(asm, "AB") // arm, arm64, ppc64
					t.blockJump[k] = asm
					if len(v.Elts) >= 3 && name(v.Elts[2]) == "true" {
						t.blockEq[k] = true
					}
				}
			case "condBits":
				for _, e := range lit.Elts {
					kv, ok := e.(*ast.KeyValueExpr)
					if !ok {
						continue
					}
					k := strings.TrimPrefix(strings.TrimPrefix(name(kv.Key), "Op"), a.Name)
					v := name(kv.Value)
					if i := strings.LastIndex(v, "_"); i >= 0 {
						v = v[i+1:]
					}
					t.condBits[k] = v
				}
			}
		}
	}
	return t
}

// category returns the flags category of a consumer, from its name:
// float consumers are named for it (LessThanF, FLT, SETGF, EQF), and
// equality tests serve both.
func category(name string, both ...string) fcat {
	for _, b := range append(both, "EQ", "NE", "Equal", "NotEqual") {
		if name == b {
			return catBoth
		}
	}
	if strings.HasSuffix(name, "F") || strings.HasPrefix(name, "F") && name != "First" ||
		strings.HasPrefix(name, "NotLess") || strings.HasPrefix(name, "NotGreater") {
		return catFloat
	}
	return catInt
}
