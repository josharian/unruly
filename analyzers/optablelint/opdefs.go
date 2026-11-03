package optablelint

import (
	"bufio"
	"os"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/josharian/unruly/rules"
)

var opNameRE = regexp.MustCompile(`\{\s*name:\s*"(\w+)"`)

// opDefs returns the positions of the op definitions of arch in the
// *ops.go files of genDir, such as AMD64Ops.go and simdAMD64ops.go.
func opDefs(genDir, arch string) map[string]rules.Pos {
	defs := make(map[string]rules.Pos)
	paths, _ := filepath.Glob(filepath.Join(genDir, "*.go"))
	for _, path := range paths {
		if opsFileArch(filepath.Base(path)) != arch {
			continue
		}
		f, err := os.Open(path)
		if err != nil {
			continue
		}
		sc := bufio.NewScanner(f)
		sc.Buffer(nil, 1<<20)
		for line := 1; sc.Scan(); line++ {
			text := sc.Text()
			m := opNameRE.FindStringSubmatch(text)
			if m == nil || strings.Contains(text, "controls:") {
				continue // not an op (blocks have controls)
			}
			if _, ok := defs[m[1]]; !ok {
				defs[m[1]] = rules.Pos{File: path, Line: line}
			}
		}
		f.Close()
	}
	return defs
}

// opsFileArch returns the arch whose ops a _gen file defines, or "".
// For example, AMD64Ops.go and simdAMD64ops.go define AMD64 ops and
// simdARM64SVEops.go defines ARM64 ops.
func opsFileArch(name string) string {
	base, ok := strings.CutSuffix(name, ".go")
	if !ok || strings.Contains(strings.ToLower(base), "generic") {
		return ""
	}
	base, ok = strings.CutSuffix(base, "Ops")
	if !ok {
		base, ok = strings.CutSuffix(base, "ops")
	}
	if !ok {
		return ""
	}
	base = strings.TrimPrefix(base, "simd")
	return strings.TrimSuffix(base, "SVE")
}
