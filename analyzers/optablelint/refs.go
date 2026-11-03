package optablelint

import (
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/josharian/unruly/ops"
)

// opRefs finds references to ops in compiler code outside the rules, such
// as ssacompile/addressingmodes.go, which produces AMD64's indexed ops.
type opRefs struct {
	compileDir string            // cmd/compile/internal
	refs       map[string]string // qualified op name to the first file that refers to it
}

// Directories of cmd/compile/internal that define or consume ops rather
// than produce them: op tables, generated rewrite code, and codegen.
var skipDirs = map[string]bool{
	"ssa/_gen": true, "ssa/gen": true, "ssa/rewrite": true,
	"amd64": true, "arm": true, "arm64": true, "loong64": true, "mips": true, "mips64": true,
	"ppc64": true, "riscv64": true, "s390x": true, "wasm": true, "x86": true,
}

var opRefRE = regexp.MustCompile(`\bOp([A-Z0-9]\w*)`)

// find returns the path, relative to cmd/compile/internal, of a file outside
// rules, op tables, and codegen that refers to op, or "".
func (r *opRefs) find(op *ops.Op) string {
	if r.refs == nil {
		r.refs = make(map[string]string)
		filepath.WalkDir(r.compileDir, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return nil
			}
			rel, _ := filepath.Rel(r.compileDir, path)
			rel = filepath.ToSlash(rel)
			if d.IsDir() {
				if skipDirs[rel] {
					return filepath.SkipDir
				}
				return nil
			}
			name := d.Name()
			if !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") ||
				name == "opGen.go" || strings.HasPrefix(name, "rewrite") {
				return nil
			}
			b, err := os.ReadFile(path)
			if err != nil {
				return nil
			}
			for _, m := range opRefRE.FindAllSubmatch(b, -1) {
				if _, ok := r.refs[string(m[1])]; !ok {
					r.refs[string(m[1])] = rel
				}
			}
			return nil
		})
	}
	return r.refs[op.QualifiedName()]
}
