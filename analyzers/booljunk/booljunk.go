// Package booljunk reports lowerings that read more of a bool's register
// than its low byte.
package booljunk

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "booljunk",
	Doc: `report lowerings that read more of a bool's register than its low byte

A bool lives in the low byte of a register; the rest of the register is
junk (see the header of each <arch>Ops.go). Under the register ABI, junk
really occurs: reflect.MakeFunc, for one, writes a bool result into only
the low byte of its register slot (internal/abi.RegArgs.IntRegArgAddr),
and on x86 SETcc writes only a byte. So a lowering of a generic op's bool
operand must look only at its low byte, as

	(If cond yes no) => (TBNZ [0] cond yes no)

does, or mask or extend it first. One that tests the whole register,
like ARM64's old

	(If cond yes no) => (NZ cond yes no)

takes a false bool with junk above bit 7 for true.

The check applies to arches with a register ABI (those whose op tables
name integer parameter registers) and 386. It tracks each variable bound
at a bool operand of a generic op (as given by opsig: If's control,
CondSelect's condition, the operands of Not, AndB, ...) through ops that
compute the result's low byte from their operands' low bytes (AND, OR,
XOR, ADD, SUB, ...), and reports it reaching a comparison, a test of the
whole register (SEQZ, MASKEQZ, ...), or a block that branches on the
register. Byte extensions, masks of at most 0xff, byte tests and compares,
and byte stores are safe.`,
	Run: run,
}

// junkArch reports whether a bool's register may hold junk above the low
// byte on arch a: on arches with a register ABI, and on 386, whose SETcc
// instructions write only a byte register.
func junkArch(a *ops.Arch) bool {
	if a.Generic {
		return false
	}
	if a.Name == "386" {
		return true
	}
	if archs, ok := regabiArches(a.Tables().Dir); ok {
		return archs[a.Name]
	}
	s, _ := a.Raw["ParamIntRegNames"].(string)
	return s != ""
}

var regabiCache struct {
	sync.Mutex
	m map[string]map[string]bool
}

// regabiArches returns the arches on which the register ABI is enabled,
// read from the cases of internal/buildcfg/exp.go that set
// regabiSupported, in the Go tree around genDir.
func regabiArches(genDir string) (map[string]bool, bool) {
	regabiCache.Lock()
	defer regabiCache.Unlock()
	if m, ok := regabiCache.m[genDir]; ok {
		return m, m != nil
	}
	if regabiCache.m == nil {
		regabiCache.m = map[string]map[string]bool{}
	}
	regabiCache.m[genDir] = nil
	src := filepath.Join(genDir, "..", "..", "..", "..", "..", "internal", "buildcfg", "exp.go")
	f, err := parser.ParseFile(token.NewFileSet(), src, nil, 0)
	if err != nil {
		return nil, false
	}
	m := map[string]bool{}
	ast.Inspect(f, func(n ast.Node) bool {
		cc, ok := n.(*ast.CaseClause)
		if !ok {
			return true
		}
		sets := false
		for _, st := range cc.Body {
			if as, ok := st.(*ast.AssignStmt); ok && len(as.Lhs) == 1 {
				if id, ok := as.Lhs[0].(*ast.Ident); ok && id.Name == "regabiSupported" {
					sets = true
				}
			}
		}
		if sets {
			for _, e := range cc.List {
				if lit, ok := e.(*ast.BasicLit); ok && lit.Kind == token.STRING {
					goarch, _ := strconv.Unquote(lit.Value)
					m[archName(goarch)] = true
				}
			}
		}
		return true
	})
	if len(m) == 0 {
		return nil, false
	}
	regabiCache.m[genDir] = m
	return m, true
}

// archName returns the SSA arch name for a GOARCH.
func archName(goarch string) string {
	goarch = strings.TrimSuffix(goarch, "le")
	return strings.ToUpper(goarch)
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		if !junkArch(set.Arch) {
			continue
		}
		for _, r := range set.Rules {
			if !r.IsBlock() && r.Match.Ellipsis {
				checkEllipsis(pass, r)
				continue
			}
			check(pass, r)
		}
	}
	return nil
}

// boolSlot reports whether arg i of the generic op is a bool.
func boolSlot(op *ops.Op, i int) bool {
	sig, ok := opsig.Lookup(op)
	if !ok || i >= len(sig.Args) {
		return false
	}
	return sig.Args[i].Kind == opsig.Bool
}

func check(pass *analysis.Pass, r *rules.Rule) {
	// Find the variables bound at bool operands of generic ops.
	junk := map[string]bool{}
	visit := func(n *rules.Value, slot bool) {
		if slot && n.IsVar() && !notBool(r, n.Name) {
			junk[n.Name] = true
		}
	}
	var walk func(n *rules.Value)
	walk = func(n *rules.Value) {
		if n.Op == nil {
			return
		}
		for i, a := range n.Args {
			visit(a, n.Op.IsGeneric() && boolSlot(n.Op, i))
			walk(a)
		}
	}
	if r.IsBlock() {
		if r.MatchBlock.Info.IsGeneric() && r.MatchBlock.Kind == "If" {
			visit(r.MatchBlock.Controls[0], true)
		}
		for _, c := range r.MatchBlock.Controls {
			walk(c)
		}
	} else {
		walk(r.Match)
	}
	if len(junk) == 0 {
		return
	}

	// Follow them through the result.
	if r.IsBlock() {
		rb := r.ResultBlock
		for _, c := range rb.Controls {
			if isJunk(c, junk) {
				if !byteTestBlock(rb) {
					pass.Reportf(r.Pos, "%s branches on the whole register of %s, a bool whose bits above the low byte may be junk; test only the low byte (or mask or zero-extend it first)",
						rb.Kind, junkName(c, junk))
					return
				}
			}
		}
		for _, c := range rb.Controls {
			if msg := uses(c, junk); msg != "" {
				pass.Report(r.Pos, msg)
				return
			}
		}
		return
	}
	if r.Result != nil {
		if msg := uses(r.Result, junk); msg != "" {
			pass.Report(r.Pos, msg)
		}
	}
}

// checkEllipsis checks a rule (Op ...) => (Op2 ...), which passes Op's
// args to Op2 in order.
func checkEllipsis(pass *analysis.Pass, r *rules.Rule) {
	if !r.Match.Op.IsGeneric() || r.Result.Op == nil {
		return
	}
	for i := range int(r.Match.Op.ArgLength) {
		if boolSlot(r.Match.Op, i) && wideReader(r.Result, i) {
			pass.Reportf(r.Pos, "%s reads the whole register of %s's arg %d, a bool whose bits above the low byte may be junk; mask or zero-extend it first",
				r.Result.Op.Name, r.Match.Op.Name, i)
			return
		}
	}
}

// notBool reports whether r's condition says that the variable x is not a
// bool, as in (CondSelect <t> x y check) && check.Type.Size() == 8.
func notBool(r *rules.Rule, x string) bool {
	for _, c := range conjuncts(r.CondExpr) {
		text := r.Cond[c.Pos()-1 : c.End()-1]
		if text == "!"+x+".Type.IsBoolean()" {
			return true
		}
		if m := sizeRE.FindStringSubmatch(text); m != nil && m[1] == x {
			n, _ := strconv.Atoi(m[3])
			switch m[2] {
			case "==":
				return n != 1
			case ">":
				return n >= 1
			case ">=":
				return n > 1
			}
		}
	}
	return false
}

var sizeRE = regexp.MustCompile(`^(\w+)\.Type\.Size\(\) *(==|>=|>) *(\d+)$`)

// conjuncts splits a condition at its top-level &&s.
func conjuncts(e ast.Expr) []ast.Expr {
	if e == nil {
		return nil
	}
	if b, ok := e.(*ast.BinaryExpr); ok && b.Op == token.LAND {
		return append(conjuncts(b.X), conjuncts(b.Y)...)
	}
	return []ast.Expr{e}
}

// isJunk reports whether n is a junk bool, or computes its low byte
// from one without looking at higher bits (a junk-preserving op).
func isJunk(n *rules.Value, junk map[string]bool) bool {
	if n.IsLeaf() {
		return junk[n.Name]
	}
	if !closedOp(n) {
		return false
	}
	for _, a := range n.Args {
		if isJunk(a, junk) {
			return true
		}
	}
	return false
}

func junkName(n *rules.Value, junk map[string]bool) string {
	if n.IsLeaf() {
		return n.Name
	}
	for _, a := range n.Args {
		if isJunk(a, junk) {
			return junkName(a, junk)
		}
	}
	return n.Text
}

// uses returns a description of a use of a junk bool in v that reads
// more than its low byte, or "".
func uses(v *rules.Value, junk map[string]bool) string {
	msg := ""
	v.Walk(func(n *rules.Value) bool {
		if msg != "" || n.Op == nil {
			return msg == ""
		}
		for i, a := range n.Args {
			if !isJunk(a, junk) {
				continue
			}
			if wideReader(n, i) {
				msg = fmt.Sprintf("%s reads the whole register of %s, a bool whose bits above the low byte may be junk; mask or zero-extend it first",
					n.Op.Name, junkName(a, junk))
				return false
			}
		}
		return true
	})
	return msg
}

var (
	// Ops whose result's low byte depends only on their operands' low
	// bytes: bitwise logic and add/subtract, in any width.
	closedRE = regexp.MustCompile(`^(AND|OR|XOR|EQV|ANDN|ORN|NOR|BIC|EON|ADD|SUB|NEG|NOT|MVN)[A-Z]*(const|I)?$`)
	// Comparisons and tests.
	compareRE = regexp.MustCompile(`^(CMP|CMN|TST|TEST)`)
	// Ops that test whether a whole register is zero.
	zeroTestRE = regexp.MustCompile(`^(SEQZ|SNEZ|MASKEQZ|MASKNEZ|CZEROEQZ|CZERONEZ)$`)
	// Byte-sized operations.
	byteRE = regexp.MustCompile(`^(CMPB|TESTB|MOVB(U|Z)?reg$|MOVB[QL][SZ]X$)`)
)

// closedOp reports whether n's low byte depends only on its args' low
// bytes, so that a junk bool arg makes a junk result (rather than a
// wrong one). AND with a mask of at most 0xff cleans its arg instead.
func closedOp(n *rules.Value) bool {
	if n.Op.Name == "Copy" {
		return true
	}
	if !closedRE.MatchString(n.Op.Name) {
		return false
	}
	if c, ok := auxLiteral(n); ok && isAndOp(n.Op.Name) && 0 <= c && c <= 0xff {
		return false
	}
	return true
}

func isAndOp(name string) bool {
	return strings.HasPrefix(name, "AND") && !strings.HasPrefix(name, "ANDN")
}

// wideReader reports whether op n reads more than the low byte of arg i.
func wideReader(n *rules.Value, i int) bool {
	name := n.Op.Name
	switch {
	case byteRE.MatchString(name):
		return false
	case compareRE.MatchString(name):
		// TST with a constant mask of at most 0xff reads only the low byte.
		if c, ok := auxLiteral(n); ok && (strings.HasPrefix(name, "TST") || strings.HasPrefix(name, "TEST")) && 0 <= c && c <= 0xff {
			return false
		}
		return true
	case zeroTestRE.MatchString(name):
		// MASKEQZ x cond and CZEROEQZ x cond test arg 1.
		if strings.HasPrefix(name, "MASK") || strings.HasPrefix(name, "CZERO") {
			return i == 1
		}
		return true
	}
	return false
}

// byteTestBlock reports whether b branches on a bit of its control's low
// byte, like ARM64's TBNZ [0].
func byteTestBlock(b *rules.Block) bool {
	switch b.Kind {
	case "TBZ", "TBNZ":
		c, err := strconv.ParseInt(b.AuxInt, 0, 64)
		return err == nil && 0 <= c && c < 8
	}
	return false
}

func auxLiteral(n *rules.Value) (int64, bool) {
	if n.AuxInt == "" {
		return 0, false
	}
	c, err := strconv.ParseInt(n.AuxInt, 0, 64)
	return c, err == nil
}
