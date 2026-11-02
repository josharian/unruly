// Package testenv locates the Go trees that tests run against.
package testenv

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/josharian/unruly/ops"
)

// GoRoot returns the Go tree whose op tables and rules tests use:
// $UNRULY_GOROOT if set, else $HOME/go/tip if it exists, else
// `go env GOROOT`. It skips the test if none has an SSA _gen directory.
func GoRoot(t testing.TB) string {
	t.Helper()
	var candidates []string
	if r := os.Getenv("UNRULY_GOROOT"); r != "" {
		candidates = []string{r}
	} else {
		if home, err := os.UserHomeDir(); err == nil {
			candidates = append(candidates, filepath.Join(home, "go", "tip"))
		}
		if out, err := exec.Command("go", "env", "GOROOT").Output(); err == nil {
			candidates = append(candidates, strings.TrimSpace(string(out)))
		}
	}
	for _, c := range candidates {
		if _, err := ops.FindGenDir(c); err == nil {
			return c
		}
	}
	t.Skipf("no Go tree with an SSA _gen directory among %q", candidates)
	return ""
}

// GenDir returns the _gen directory of GoRoot.
func GenDir(t testing.TB) string {
	t.Helper()
	dir, err := ops.FindGenDir(GoRoot(t))
	if err != nil {
		t.Fatal(err)
	}
	return dir
}

// GoRepo returns a Go git repository for tests of historical revisions:
// $UNRULY_GOREPO if set, else $HOME/go/tip. It skips the test if that is
// not a git repository.
func GoRepo(t testing.TB) string {
	t.Helper()
	repo := os.Getenv("UNRULY_GOREPO")
	if repo == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			t.Skip("no home directory")
		}
		repo = filepath.Join(home, "go", "tip")
	}
	if _, err := os.Stat(filepath.Join(repo, ".git")); err != nil {
		t.Skipf("no Go git repository at %s (set UNRULY_GOREPO)", repo)
	}
	return repo
}
