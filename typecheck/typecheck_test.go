package typecheck_test

import (
	"os/exec"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// checkAll checks that every rule in the Go tree at path type-checks.
func checkAll(t *testing.T, path string) {
	c, err := rules.Load(path)
	if err != nil {
		t.Fatal(err)
	}
	n := 0
	for _, set := range c.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			t.Errorf("%s: %v", set, err)
			continue
		}
		for _, err := range res.Errors {
			t.Errorf("%s: %v", set, err)
		}
		for _, r := range set.Rules {
			n++
			tr := res.Rule(r)
			for _, err := range tr.Errors {
				t.Errorf("%s: %s: %v", r.Pos, r.Text, err)
			}
			for _, m := range missingExprs(r, tr) {
				t.Errorf("%s: %s: no typed expression for %s", r.Pos, r.Text, m)
			}
		}
	}
	t.Logf("%s: %d rules", path, n)
}

func TestGoRoot(t *testing.T) {
	checkAll(t, testenv.GoRoot(t))
}

func TestInstalledGo(t *testing.T) {
	out, err := exec.Command("go", "env", "GOROOT").Output()
	if err != nil {
		t.Skip("no go command")
	}
	root := strings.TrimSpace(string(out))
	if _, err := ops.FindGenDir(root); err != nil {
		t.Skip(err)
	}
	checkAll(t, root)
}

func TestHistorical(t *testing.T) {
	if testing.Short() {
		t.Skip("slow")
	}
	repo := testenv.GoRepo(t)
	for _, rev := range []string{"79a3482d9e", "go1.20", "go1.24.0"} {
		t.Run(rev, func(t *testing.T) {
			dir, err := gitrev.GenDir(repo, rev)
			if err != nil {
				t.Fatal(err)
			}
			checkAll(t, dir)
		})
	}
}

// missingExprs lists the expressions of r that tr lacks.
func missingExprs(r *rules.Rule, tr *typecheck.Rule) []string {
	var missing []string
	need := func(ok bool, what string) {
		if !ok {
			missing = append(missing, what)
		}
	}
	need(r.Cond == "" || tr.Cond != nil, "cond")
	need(r.ResultCode == "" || tr.Code != nil, "code")
	need(r.Placement == "" || tr.Placement != nil, "placement")
	field := func(node any, f typecheck.Field, text string) {
		if text != "" && text != "_" {
			need(tr.Expr(node, f) != nil, text)
		}
	}
	var walk func(v *rules.Value, match bool)
	walk = func(v *rules.Value, match bool) {
		if v.Name != "" && (match || v.IsLeaf() || v != r.Result || r.Placement != "") {
			field(v, typecheck.Name, v.Name)
		}
		field(v, typecheck.Type, v.Type)
		field(v, typecheck.AuxInt, v.AuxInt)
		field(v, typecheck.Aux, v.Aux)
		for _, a := range v.Args {
			walk(a, match)
		}
	}
	if r.IsBlock() {
		field(r.MatchBlock, typecheck.AuxInt, r.MatchBlock.AuxInt)
		field(r.MatchBlock, typecheck.Aux, r.MatchBlock.Aux)
		field(r.ResultBlock, typecheck.AuxInt, r.ResultBlock.AuxInt)
		field(r.ResultBlock, typecheck.Aux, r.ResultBlock.Aux)
	}
	for _, v := range r.MatchValues() {
		walk(v, true)
	}
	for _, v := range r.ResultValues() {
		walk(v, false)
	}
	return missing
}
