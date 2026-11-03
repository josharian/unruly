package simdcodegen_test

import (
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// runFixture runs a on synthetic op tables for arches, with no rules, and
// checks its diagnostics against the // want comments of the files in
// genDir, which hold the arches' op definitions.
func runFixture(t *testing.T, genDir string, a *analysis.Analyzer, arches ...*ops.Arch) {
	t.Helper()
	tables := &ops.Tables{Dir: genDir, Generic: &ops.Arch{Name: "generic", Generic: true}}
	var sets []*rules.RuleSet
	for _, arch := range arches {
		for _, op := range arch.Ops {
			op.Arch = arch
		}
		tables.Archs = append(tables.Archs, arch)
		sets = append(sets, &rules.RuleSet{Arch: arch})
	}
	c := &rules.Corpus{Ops: tables, Sets: sets}
	diags, err := analysis.Run(c, sets, []*analysis.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}

	type key struct {
		file string
		line int
	}
	wants := make(map[key][]*regexp.Regexp)
	paths, _ := filepath.Glob(filepath.Join(genDir, "*.go"))
	for _, p := range paths {
		b, err := os.ReadFile(p)
		if err != nil {
			t.Fatal(err)
		}
		for i, line := range strings.Split(string(b), "\n") {
			_, rest, ok := strings.Cut(line, "// want ")
			if !ok {
				continue
			}
			q, err := strconv.QuotedPrefix(strings.TrimSpace(rest))
			if err != nil {
				t.Fatalf("%s:%d: malformed want comment", p, i+1)
			}
			s, _ := strconv.Unquote(q)
			wants[key{p, i + 1}] = append(wants[key{p, i + 1}], regexp.MustCompile(s))
		}
	}
	for _, d := range diags {
		k := key{d.Pos.File, d.Pos.Line}
		res := wants[k]
		found := false
		for i, re := range res {
			if re.MatchString(d.Message) {
				wants[k] = append(res[:i:i], res[i+1:]...)
				found = true
				break
			}
		}
		if !found {
			t.Errorf("unexpected diagnostic: %v", d)
		}
	}
	for k, res := range wants {
		for _, re := range res {
			t.Errorf("%s:%d: no diagnostic matching %q", k.file, k.line, re)
		}
	}
}
