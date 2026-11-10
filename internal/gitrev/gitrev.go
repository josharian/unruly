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
	"time"
)

// GenDir extracts the source tree (src, without testdata) at revision rev
// of the Go repository repo, and returns the location of its SSA rules
// directory (src/cmd/compile/internal/ssa/_gen, or .../gen in older trees).
// Extracted trees are cached by commit hash in the user cache directory.
func GenDir(repo, rev string) (string, error) {
	hash, err := resolve(repo, rev)
	if err != nil {
		return "", err
	}
	src, err := extract(repo, hash, "src", ":(exclude)src/**/testdata/**")
	if err != nil {
		return "", err
	}
	for _, sub := range []string{"_gen", "gen"} {
		p := filepath.Join(src, "cmd", "compile", "internal", "ssa", sub)
		if _, err := os.Stat(filepath.Join(p, "genericOps.go")); err == nil {
			return p, nil
		}
	}
	return "", fmt.Errorf("%s at %s has no SSA rules directory", repo, rev)
}

func resolve(repo, rev string) (string, error) {
	out, err := exec.Command("git", "-C", repo, "rev-parse", "--verify", "--end-of-options", rev+"^{commit}").Output()
	if err != nil {
		return "", fmt.Errorf("resolving %s in %s: %v", rev, repo, gitErr(err))
	}
	return strings.TrimSpace(string(out)), nil
}

func extract(repo, hash, dir string, pathspecs ...string) (string, error) {
	cache, err := os.UserCacheDir()
	if err != nil {
		return "", err
	}
	root := filepath.Join(cache, "unruly", "rev", hash, strings.ReplaceAll(dir, "/", "_"))
	final := filepath.Join(root, filepath.FromSlash(dir))
	if _, err := os.Stat(final); err == nil {
		touch(filepath.Dir(root))
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

	args := append([]string{"-C", repo, "archive", "--format=tar", hash, dir}, pathspecs...)
	cmd := exec.Command("git", args...)
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

// touch marks a cache entry as used, so that cache cleaners can prune
// entries by age. Like the go command's build cache, it updates the
// modification time at most once an hour.
func touch(path string) {
	now := time.Now()
	if fi, err := os.Stat(path); err == nil && now.Sub(fi.ModTime()) > time.Hour {
		os.Chtimes(path, now, now)
	}
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
