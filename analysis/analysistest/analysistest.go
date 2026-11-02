// Package analysistest tests analyzers against fixture rules files and
// against historical revisions of the Go repository.
package analysistest

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// Tables returns the op tables of the Go tree that tests run against:
// $UNRULY_GOROOT if set, else $HOME/go/tip if it exists, else
// `go env GOROOT`. It skips the test if there is none.
func Tables(t testing.TB) *ops.Tables {
	t.Helper()
	tables, err := ops.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	return tables
}

// Run applies a to the *.rules files in dir and checks its diagnostics
// against the files' // want comments. It returns the diagnostics.
//
// Each file's base name determines its arch and rule set, exactly as in a
// _gen directory (generic.rules, AMD64.rules, AMD64latelower.rules,
// simdAMD64.rules, ...). Ops are resolved using Tables.
//
// A comment of the form
//
//	// want "regexp" `regexp` ...
//
// expects, for each quoted regexp, one diagnostic on that line whose message
// matches it. Diagnostics are usually reported at a rule's first line, so put
// the comment there. Lines without a want comment must have no diagnostics.
func Run(t *testing.T, dir string, a *analysis.Analyzer) []analysis.Diagnostic {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join(dir, "*.rules"))
	if err != nil {
		t.Fatal(err)
	}
	if len(paths) == 0 {
		t.Fatalf("no .rules files in %s", dir)
	}
	files := make(map[string]string)
	for _, p := range paths {
		b, err := os.ReadFile(p)
		if err != nil {
			t.Fatal(err)
		}
		files[p] = string(b)
	}
	return RunFiles(t, files, a)
}

// RunFiles is like Run, but takes the rules files' contents keyed by path.
// For example:
//
//	analysistest.RunFiles(t, map[string]string{
//		"generic.rules": `(Neg64 (Neg64 x)) => x // want "..."`,
//	}, myanalyzer.Analyzer)
func RunFiles(t *testing.T, files map[string]string, a *analysis.Analyzer) []analysis.Diagnostic {
	t.Helper()
	tables := Tables(t)
	src := make(map[string][]byte)
	for p, s := range files {
		src[p] = []byte(s)
	}
	c := rules.Parse(tables, src)
	for _, err := range c.Errors {
		t.Errorf("parse error: %v", err)
	}
	if t.Failed() {
		t.FailNow()
	}
	diags, err := analysis.Run(c, c.Sets, []*analysis.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}

	type key struct {
		file string
		line int
	}
	wants := make(map[key][]*regexp.Regexp)
	for p, s := range files {
		for i, line := range strings.Split(s, "\n") {
			res, err := parseWant(line)
			if err != nil {
				t.Fatalf("%s:%d: %v", p, i+1, err)
			}
			if len(res) > 0 {
				wants[key{p, i + 1}] = res
			}
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
	return diags
}

// parseWant parses the regexps of a // want comment in line, if any.
func parseWant(line string) ([]*regexp.Regexp, error) {
	_, rest, ok := strings.Cut(line, "// want ")
	if !ok {
		return nil, nil
	}
	var res []*regexp.Regexp
	rest = strings.TrimSpace(rest)
	for rest != "" {
		q, err := strconv.QuotedPrefix(rest)
		if err != nil {
			return nil, fmt.Errorf("malformed want comment: %q", rest)
		}
		s, _ := strconv.Unquote(q)
		re, err := regexp.Compile(s)
		if err != nil {
			return nil, err
		}
		res = append(res, re)
		rest = strings.TrimSpace(rest[len(q):])
	}
	if len(res) == 0 {
		return nil, fmt.Errorf("want comment without patterns")
	}
	return res, nil
}

// Survey applies a to the rules of the Go tree that tests use (see Tables)
// and logs each diagnostic, for exploring an analyzer's findings on real
// rules during development without building cmd/unruly:
//
//	func TestSurvey(t *testing.T) { analysistest.Survey(t, myanalyzer.Analyzer) }
//
//	go test -v -run Survey ./analyzers/myanalyzer
//
// Set UNRULY_GOROOT to survey a different tree. Parse errors fail the test.
func Survey(t *testing.T, a *analysis.Analyzer) []analysis.Diagnostic {
	t.Helper()
	c, err := rules.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	return survey(t, c, a)
}

// SurveyRevision is like Survey, for a revision of the Go repository
// (see RunRevision).
func SurveyRevision(t *testing.T, rev string, a *analysis.Analyzer) []analysis.Diagnostic {
	t.Helper()
	dir, err := gitrev.GenDir(testenv.GoRepo(t), rev)
	if err != nil {
		t.Fatal(err)
	}
	c, err := rules.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	return survey(t, c, a)
}

func survey(t *testing.T, c *rules.Corpus, a *analysis.Analyzer) []analysis.Diagnostic {
	t.Helper()
	for _, err := range c.Errors {
		t.Errorf("parse error: %v", err)
	}
	diags, err := analysis.Run(c, c.Sets, []*analysis.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	for _, d := range diags {
		t.Log(d)
	}
	t.Logf("%d diagnostics", len(diags))
	return diags
}

// Want is an expectation about a diagnostic in a historical revision.
type Want struct {
	// File is the base name of the rules file, such as "AMD64.rules".
	File string
	// Line is the first line of the rule. If Line is 0, Rule identifies the
	// rule instead: a substring of its source text (whitespace-normalized,
	// before | expansion) that occurs in exactly one rule in File.
	Line int
	Rule string
	// Message is a regexp the diagnostic's message must match.
	// The empty string matches any message.
	Message string
	// Absent asserts that there is no matching diagnostic at the rule.
	Absent bool
}

// RunRevision applies a to the rules at revision rev of the Go repository
// (from testenv: $UNRULY_GOREPO, else $HOME/go/tip; the test is skipped if it
// does not exist), using that revision's own op tables, and checks wants.
// It returns the diagnostics. Parse errors fail the test.
//
// The repository is only read; the revision is extracted to the user cache
// directory.
func RunRevision(t *testing.T, rev string, a *analysis.Analyzer, wants ...Want) []analysis.Diagnostic {
	t.Helper()
	repo := testenv.GoRepo(t)
	dir, err := gitrev.GenDir(repo, rev)
	if err != nil {
		t.Fatal(err)
	}
	c, err := rules.Load(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, err := range c.Errors {
		t.Errorf("%s: parse error: %v", rev, err)
	}
	diags, err := analysis.Run(c, c.Sets, []*analysis.Analyzer{a})
	if err != nil {
		t.Fatal(err)
	}
	for _, w := range wants {
		line := w.Line
		if line == 0 {
			line = findRule(t, c, w.File, w.Rule)
		}
		re, err := regexp.Compile(w.Message)
		if err != nil {
			t.Fatal(err)
		}
		var found []analysis.Diagnostic
		for _, d := range diags {
			if filepath.Base(d.Pos.File) == w.File && d.Pos.Line == line && re.MatchString(d.Message) {
				found = append(found, d)
			}
		}
		switch {
		case w.Absent && len(found) > 0:
			t.Errorf("%s: unexpected diagnostic at %s:%d: %v", rev, w.File, line, found)
		case !w.Absent && len(found) == 0:
			var near []string
			for _, d := range diags {
				if filepath.Base(d.Pos.File) == w.File && d.Pos.Line == line {
					near = append(near, d.Message)
				}
			}
			t.Errorf("%s: no diagnostic matching %q at %s:%d (diagnostics there: %q)", rev, w.Message, w.File, line, near)
		}
	}
	return diags
}

// findRule returns the line of the unique rule in file whose source text
// contains text.
func findRule(t *testing.T, c *rules.Corpus, file, text string) int {
	t.Helper()
	text = strings.Join(strings.Fields(text), " ")
	lines := map[int]bool{}
	for _, s := range c.Sets {
		for _, f := range s.Files {
			if filepath.Base(f.Path) != file {
				continue
			}
			for _, r := range f.Rules {
				if strings.Contains(r.Orig, text) {
					lines[r.Pos.Line] = true
				}
			}
		}
	}
	if len(lines) != 1 {
		t.Fatalf("%d rules in %s contain %q, want exactly 1", len(lines), file, text)
	}
	for l := range lines {
		return l
	}
	panic("unreachable")
}
