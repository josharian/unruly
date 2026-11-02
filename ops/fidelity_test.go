package ops_test

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
)

// The fidelity tests compare the loaded tables against the opcode table
// that rulegen generated from the same _gen sources (opGen.go).

func TestFidelityGoRoot(t *testing.T) {
	checkFidelity(t, filepath.Join(testenv.GoRoot(t), "src", "cmd", "compile", "internal", "ssa"))
}

func TestFidelityHistorical(t *testing.T) {
	repo := testenv.GoRepo(t)
	for _, date := range []string{"2020-11-01", "2022-06-01", "2024-06-01"} {
		t.Run(date, func(t *testing.T) {
			out, err := exec.Command("git", "-C", repo, "log", "-1", "--format=%H", "--before="+date).Output()
			if err != nil {
				t.Fatal(err)
			}
			dir, err := gitrev.Extract(repo, strings.TrimSpace(string(out)), "src/cmd/compile/internal/ssa")
			if err != nil {
				t.Fatal(err)
			}
			checkFidelity(t, dir)
		})
	}
}

type genOp struct {
	fields                    map[string]string // lowercased key -> expr text
	inputs, outputs, clobbers string
}

func checkFidelity(t *testing.T, ssaDir string) {
	var genDir string
	for _, sub := range []string{"_gen", "gen"} {
		if d, err := ops.FindGenDir(filepath.Join(ssaDir, sub)); err == nil {
			genDir = d
		}
	}
	tables, err := ops.Load(genDir)
	if err != nil {
		t.Fatal(err)
	}
	want := opcodeTable(t, ssaDir)

	var got []*ops.Op
	for _, a := range tables.Archs {
		for _, op := range a.Ops {
			if op.Name != "Invalid" {
				got = append(got, op)
			}
		}
	}
	if len(got) != len(want) {
		t.Fatalf("loaded %d ops, opcodeTable has %d", len(got), len(want))
	}
	nerr := 0
	for i, op := range got {
		w := want[i]
		check := func(field, gotv string) {
			wantv := w.fields[field]
			if field == "auxtype" {
				wantv = strings.TrimPrefix(strings.TrimPrefix(wantv, "AuxType"), "aux")
				gotv = strings.ToLower(gotv)
				wantv = strings.ToLower(wantv)
			}
			if gotv != wantv && nerr < 20 {
				nerr++
				t.Errorf("%s: %s = %q, opcodeTable has %q", op, field, gotv, wantv)
			}
		}
		b := func(x bool) string {
			if x {
				return "true"
			}
			return ""
		}
		check("name", strconv.Quote(op.Name))
		check("arglen", strconv.Itoa(int(op.ArgLength)))
		check("auxtype", op.Aux)
		check("commutative", b(op.Commutative))
		check("resultinarg0", b(op.ResultInArg0))
		check("clobberflags", b(op.ClobberFlags))
		check("call", b(op.Call))
		check("faultonnilarg0", b(op.FaultOnNilArg0))
		check("hassideeffects", b(op.HasSideEffects))
		if op.IsGeneric() {
			continue
		}
		masks := func(l []ops.RegMask) string {
			var s []string
			for i, m := range l {
				if !m.Empty() {
					s = append(s, fmt.Sprintf("%d:%d/%d", i, m.Lo, m.Hi))
				}
			}
			return strings.Join(s, " ")
		}
		if g := masks(op.Reg.Inputs); g != w.inputs && nerr < 20 {
			nerr++
			t.Errorf("%s: inputs %s, opcodeTable has %s", op, g, w.inputs)
		}
		if g := masks(op.Reg.Outputs); g != w.outputs && nerr < 20 {
			nerr++
			t.Errorf("%s: outputs %s, opcodeTable has %s", op, g, w.outputs)
		}
		if g := masks([]ops.RegMask{op.Reg.Clobbers}); g != w.clobbers && nerr < 20 {
			nerr++
			t.Errorf("%s: clobbers %s, opcodeTable has %s", op, g, w.clobbers)
		}
	}
	t.Logf("%s: %d ops match", ssaDir, len(got))
}

// opcodeTable parses the opcode table in the generated opGen.go.
func opcodeTable(t *testing.T, ssaDir string) []genOp {
	file := filepath.Join(ssaDir, "ssaop", "opGen.go")
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
	if err != nil {
		file = filepath.Join(ssaDir, "opGen.go")
		f, err = parser.ParseFile(fset, file, nil, parser.SkipObjectResolution)
	}
	if err != nil {
		t.Fatal(err)
	}
	text := func(x ast.Expr) string {
		var b strings.Builder
		ast.Inspect(x, func(n ast.Node) bool {
			switch n := n.(type) {
			case *ast.BasicLit:
				b.WriteString(n.Value)
			case *ast.Ident:
				b.WriteString(n.Name)
			case *ast.UnaryExpr:
				b.WriteString(n.Op.String())
			}
			return true
		})
		return b.String()
	}
	// mask decodes 123 or RegMask{V1: 123, V2: 4}.
	mask := func(x ast.Expr) string {
		if cl, ok := x.(*ast.CompositeLit); ok {
			var v1, v2 string = "0", "0"
			for _, e := range cl.Elts {
				kv := e.(*ast.KeyValueExpr)
				switch strings.ToLower(text(kv.Key)) {
				case "v1":
					v1 = text(kv.Value)
				case "v2":
					v2 = text(kv.Value)
				}
			}
			return v1 + "/" + v2
		}
		return text(x) + "/0"
	}
	regList := func(x ast.Expr) string {
		m := map[int]string{}
		max := -1
		for _, e := range x.(*ast.CompositeLit).Elts {
			pair := e.(*ast.CompositeLit).Elts
			i, _ := strconv.Atoi(text(pair[0]))
			m[i] = mask(pair[1])
			max = maxInt(max, i)
		}
		var s []string
		for i := 0; i <= max; i++ {
			if v, ok := m[i]; ok && v != "0/0" {
				s = append(s, fmt.Sprintf("%d:%s", i, v))
			}
		}
		return strings.Join(s, " ")
	}
	var table *ast.CompositeLit
	for _, d := range f.Decls {
		gd, ok := d.(*ast.GenDecl)
		if !ok {
			continue
		}
		for _, s := range gd.Specs {
			vs, ok := s.(*ast.ValueSpec)
			if ok && strings.EqualFold(vs.Names[0].Name, "opcodeTable") {
				table = vs.Values[0].(*ast.CompositeLit)
			}
		}
	}
	if table == nil {
		t.Fatalf("no opcodeTable in %s", file)
	}
	var res []genOp
	for _, e := range table.Elts[1:] { // skip OpInvalid
		op := genOp{fields: map[string]string{}}
		for _, kv := range e.(*ast.CompositeLit).Elts {
			kv := kv.(*ast.KeyValueExpr)
			k := strings.ToLower(text(kv.Key))
			if k != "reg" {
				op.fields[k] = text(kv.Value)
				continue
			}
			for _, rkv := range kv.Value.(*ast.CompositeLit).Elts {
				rkv := rkv.(*ast.KeyValueExpr)
				switch strings.ToLower(text(rkv.Key)) {
				case "inputs":
					op.inputs = regList(rkv.Value)
				case "outputs":
					op.outputs = regList(rkv.Value)
				case "clobbers":
					if m := mask(rkv.Value); m != "0/0" {
						op.clobbers = "0:" + m
					}
				}
			}
		}
		if op.fields["arglen"] == "" {
			op.fields["arglen"] = "0"
		}
		res = append(res, op)
	}
	return res
}

func maxInt(a, b int) int {
	if a > b {
		return a
	}
	return b
}
