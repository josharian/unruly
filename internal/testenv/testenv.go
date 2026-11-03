// Package testenv locates the Go tree that tests run against.
package testenv

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/josharian/unruly/ops"
)

// GoRoot returns $UNRULY_GOROOT, the Go checkout whose op tables and rules
// tests use. It fails the test if that is unset or not a Go source tree.
//
// There is deliberately no default: fixtures resolve ops against this tree,
// and historical tests extract revisions from its git repository, so a
// silently chosen tree (such as an older installed Go) would give confusing
// results.
func GoRoot(t testing.TB) string {
	t.Helper()
	root := os.Getenv("UNRULY_GOROOT")
	if root == "" {
		t.Fatal("set UNRULY_GOROOT to a git checkout of Go tip, e.g. UNRULY_GOROOT=~/go go test ./...")
	}
	if _, err := os.Stat(filepath.Join(root, "src", "cmd", "compile")); err != nil {
		t.Fatalf("UNRULY_GOROOT=%s is not a Go source tree (want a directory containing src/cmd/compile)", root)
	}
	return root
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

// GoRepo returns GoRoot, for tests of historical revisions.
// It fails the test if GoRoot is not a git repository.
func GoRepo(t testing.TB) string {
	t.Helper()
	root := GoRoot(t)
	if _, err := os.Stat(filepath.Join(root, ".git")); err != nil {
		t.Fatalf("UNRULY_GOROOT=%s is not a git checkout; historical tests need one", root)
	}
	return root
}
