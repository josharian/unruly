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
			for _, err := range res.Rule(r).Errors {
				t.Errorf("%s: %s: %v", r.Pos, r.Text, err)
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
