// Package gitrev extracts directories of historical revisions of a Go
// repository, without touching the repository's working tree.
package gitrev

import (
	"archive/tar"
	"errors"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"strings"
)

// GenDir extracts the SSA rules directory (src/cmd/compile/internal/ssa/_gen,
// or .../gen in older trees) at revision rev of the Go repository repo,
// and returns its location.
func GenDir(repo, rev string) (string, error) {
	hash, err := resolve(repo, rev)
	if err != nil {
		return "", err
	}
	for _, sub := range []string{"_gen", "gen"} {
		p := "src/cmd/compile/internal/ssa/" + sub
		if exists(repo, hash, p) {
			return extract(repo, hash, p)
		}
	}
	return "", fmt.Errorf("%s at %s has no SSA rules directory", repo, rev)
}

// Extract extracts directory dir (relative to the repository root) at
// revision rev of repo, and returns its location. Extracted trees are cached
// by commit hash in the user cache directory.
func Extract(repo, rev, dir string) (string, error) {
	hash, err := resolve(repo, rev)
	if err != nil {
		return "", err
	}
	return extract(repo, hash, dir)
}

func resolve(repo, rev string) (string, error) {
	out, err := exec.Command("git", "-C", repo, "rev-parse", "--verify", "--end-of-options", rev+"^{commit}").Output()
	if err != nil {
		return "", fmt.Errorf("resolving %s in %s: %v", rev, repo, gitErr(err))
	}
	return strings.TrimSpace(string(out)), nil
}

func exists(repo, hash, dir string) bool {
	out, err := exec.Command("git", "-C", repo, "ls-tree", "-d", "--name-only", hash, dir).Output()
	return err == nil && strings.TrimSpace(string(out)) == dir
}

func extract(repo, hash, dir string) (string, error) {
	cache, err := os.UserCacheDir()
	if err != nil {
		return "", err
	}
	root := filepath.Join(cache, "unruly", "rev", hash, strings.ReplaceAll(dir, "/", "_"))
	final := filepath.Join(root, filepath.FromSlash(dir))
	if _, err := os.Stat(final); err == nil {
		return final, nil
	}
	if err := os.MkdirAll(filepath.Dir(root), 0o777); err != nil {
		return "", err
	}
	tmp, err := os.MkdirTemp(filepath.Dir(root), "tmp-")
	if err != nil {
		return "", err
	}
	defer os.RemoveAll(tmp)

	cmd := exec.Command("git", "-C", repo, "archive", "--format=tar", hash, dir)
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return "", err
	}
	var stderr strings.Builder
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		return "", err
	}
	untarErr := untar(stdout, tmp)
	io.Copy(io.Discard, stdout)
	if err := cmd.Wait(); err != nil {
		return "", fmt.Errorf("git archive %s %s: %v: %s", hash, dir, err, stderr.String())
	}
	if untarErr != nil {
		return "", untarErr
	}
	if err := os.Rename(tmp, root); err != nil && !errors.Is(err, os.ErrExist) {
		if _, statErr := os.Stat(final); statErr != nil {
			return "", err
		}
	}
	return final, nil
}

func untar(r io.Reader, dst string) error {
	tr := tar.NewReader(r)
	for {
		h, err := tr.Next()
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		name := path.Clean(h.Name)
		if path.IsAbs(name) || name == ".." || strings.HasPrefix(name, "../") {
			return fmt.Errorf("bad path in archive: %q", h.Name)
		}
		p := filepath.Join(dst, filepath.FromSlash(name))
		switch h.Typeflag {
		case tar.TypeDir:
			if err := os.MkdirAll(p, 0o777); err != nil {
				return err
			}
		case tar.TypeReg:
			if err := os.MkdirAll(filepath.Dir(p), 0o777); err != nil {
				return err
			}
			f, err := os.Create(p)
			if err != nil {
				return err
			}
			_, err = io.Copy(f, tr)
			if cerr := f.Close(); err == nil {
				err = cerr
			}
			if err != nil {
				return err
			}
		}
	}
}

func gitErr(err error) error {
	var ee *exec.ExitError
	if errors.As(err, &ee) && len(ee.Stderr) > 0 {
		return fmt.Errorf("%v: %s", err, strings.TrimSpace(string(ee.Stderr)))
	}
	return err
}
