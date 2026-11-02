package rules_test

import (
	"bufio"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

// The fidelity tests check the parser against rulegen itself: rulegen
// records every rule it compiles as "// match:", "// cond:", and
// "// result:" comments in the generated rewrite functions, one function
// per op and one switch case per block kind. Parsing the rules must
// reproduce exactly those groups, in order.

func TestFidelityGoRoot(t *testing.T) {
	root := testenv.GoRoot(t)
	checkFidelity(t, filepath.Join(root, "src", "cmd", "compile", "internal", "ssa"))
}

func TestFidelityInstalledGo(t *testing.T) {
	out, err := exec.Command("go", "env", "GOROOT").Output()
	if err != nil {
		t.Skip("no go command")
	}
	root := strings.TrimSpace(string(out))
	if _, err := ops.FindGenDir(root); err != nil {
		t.Skip(err)
	}
	checkFidelity(t, filepath.Join(root, "src", "cmd", "compile", "internal", "ssa"))
}

// historicalRevs are revisions spanning the era of typed (=>) rules,
// identified by date so that they resolve in any clone.
var historicalRevs = []string{
	"79a3482d9e", // untyped (->) rules removed; gen/
	"2021-06-01",
	"2022-06-01",
	"2023-06-01", // _gen/
	"2024-06-01",
	"2025-06-01",
}

func TestFidelityHistorical(t *testing.T) {
	if testing.Short() {
		t.Skip("slow")
	}
	repo := testenv.GoRepo(t)
	for _, date := range historicalRevs {
		t.Run(date, func(t *testing.T) {
			rev := date
			if strings.Contains(date, "-") {
				out, err := exec.Command("git", "-C", repo, "log", "-1", "--format=%H", "--before="+date).Output()
				if err != nil {
					t.Fatal(err)
				}
				rev = strings.TrimSpace(string(out))
			}
			dir, err := genDirParent(gitrev.GenDir(repo, rev))
			if err != nil {
				t.Fatal(err)
			}
			checkFidelity(t, dir)
		})
	}
}

type ruleComment struct{ match, cond, result string }

func (c ruleComment) String() string {
	if c.cond == "" {
		return c.match + " => " + c.result
	}
	return c.match + " && " + c.cond + " => " + c.result
}

var (
	genHeaderRx = regexp.MustCompile(`^// Code generated from _?gen/(\w+)\.rules`)
	valueFuncRx = regexp.MustCompile(`^func rewriteValue\w*?_Op(\w+)\(`)
	blockFuncRx = regexp.MustCompile(`^func (?:rewriteBlock\w*|RewriteBlock)\(`)
	blockCaseRx = regexp.MustCompile(`^\tcase (?:block\.)?Block(\w+):`)
	opCaseRx    = regexp.MustCompile(`^\tcase (?:ssaop\.)?Op(\w+):`)
	ellipsisRx  = regexp.MustCompile(`^\t\tv\.Op = (?:ssaop\.)?Op(\w+)$`)
	commentRx   = regexp.MustCompile(`^\s*// (match|cond|result): (.*)$`)
)

// generated parses rulegen's output files in ssaDir, returning the rule
// comments of each set, grouped by "Op<name>" or "Block<name>", and the
// ellipsis rules as "Op<from> -> Op<to>".
func generated(t *testing.T, ssaDir string) map[string]map[string][]ruleComment {
	files, _ := filepath.Glob(filepath.Join(ssaDir, "rewrite*.go"))
	more, _ := filepath.Glob(filepath.Join(ssaDir, "rewrite", "*", "rewrite*.go"))
	files = append(files, more...)
	sets := make(map[string]map[string][]ruleComment)
	for _, file := range files {
		f, err := os.Open(file)
		if err != nil {
			t.Fatal(err)
		}
		sc := bufio.NewScanner(f)
		sc.Buffer(nil, 1<<20)
		var groups map[string][]ruleComment
		group, lastOpCase, prevLine := "", "", ""
		inBlock := false
		for sc.Scan() {
			line := sc.Text()
			if line == "}" && strings.HasPrefix(group, "Op") && !inBlock {
				// rulegen ends an op's function with "return false"
				// iff its last rule can fail.
				k := group + " canfail"
				groups[k] = append(groups[k], ruleComment{match: strconv.FormatBool(prevLine == "\treturn false")})
			}
			if line != "" {
				prevLine = line
			}
			if groups == nil {
				m := genHeaderRx.FindStringSubmatch(line)
				if m == nil {
					break // not a generated rewrite file
				}
				groups = make(map[string][]ruleComment)
				sets[m[1]] = groups
				continue
			}
			if m := valueFuncRx.FindStringSubmatch(line); m != nil {
				group, inBlock = "Op"+m[1], false
				continue
			}
			if blockFuncRx.MatchString(line) {
				group, inBlock = "", true
				continue
			}
			if inBlock {
				if m := blockCaseRx.FindStringSubmatch(line); m != nil {
					group = "Block" + m[1]
					continue
				}
			} else if group == "" {
				if m := opCaseRx.FindStringSubmatch(line); m != nil {
					lastOpCase = m[1]
					continue
				}
				if m := ellipsisRx.FindStringSubmatch(line); m != nil && lastOpCase != "" {
					k := "Op" + lastOpCase + " -> Op" + m[1]
					groups[k] = append(groups[k], ruleComment{})
					continue
				}
				lastOpCase = ""
			}
			m := commentRx.FindStringSubmatch(line)
			if m == nil || group == "" {
				continue
			}
			l := groups[group]
			switch m[1] {
			case "match":
				groups[group] = append(l, ruleComment{match: m[2]})
			case "cond":
				l[len(l)-1].cond = m[2]
			case "result":
				l[len(l)-1].result = m[2]
			}
		}
		f.Close()
		if err := sc.Err(); err != nil {
			t.Fatal(err)
		}
	}
	return sets
}

func checkFidelity(t *testing.T, ssaDir string) {
	want := generated(t, ssaDir)
	if len(want) == 0 {
		t.Fatalf("no generated rewrite files in %s", ssaDir)
	}
	genDir, err := ops.FindGenDir(filepath.Join(ssaDir, "_gen"))
	if err != nil {
		genDir, err = ops.FindGenDir(filepath.Join(ssaDir, "gen"))
	}
	if err != nil {
		t.Fatal(err)
	}
	c, err := rules.Load(genDir)
	if err != nil {
		t.Fatal(err)
	}
	for _, e := range c.Errors {
		t.Errorf("parse error: %v", e)
	}
	got := make(map[string]map[string][]ruleComment)
	nrules := 0
	for _, s := range c.Sets {
		groups := make(map[string][]ruleComment)
		got[s.Name()] = groups
		for _, r := range s.Rules {
			nrules++
			var k string
			switch {
			case r.IsBlock():
				k = "Block" + r.MatchBlock.Info.QualifiedName()
			case r.Match.Ellipsis:
				groups["Op"+r.Match.Op.QualifiedName()+" -> Op"+r.Result.Op.QualifiedName()] = []ruleComment{{}}
				continue
			default:
				k = "Op" + r.Match.Op.QualifiedName()
			}
			groups[k] = append(groups[k], ruleComment{r.MatchText, r.Cond, r.ResultText})
		}
		for op, rs := range s.ByOp {
			if !rs[0].Match.Ellipsis {
				k := "Op" + op.QualifiedName() + " canfail"
				groups[k] = []ruleComment{{match: strconv.FormatBool(!rs[len(rs)-1].Unconditional())}}
			}
		}
	}
	for _, name := range sortedKeys(want) {
		if got[name] == nil {
			t.Errorf("%s: generated rewrite file but no rules parsed", name)
		}
	}
	for _, name := range sortedKeys(got) {
		w, g := want[name], got[name]
		if w == nil {
			t.Errorf("%s: rules parsed but no generated rewrite file", name)
			continue
		}
		nerr := 0
		for _, k := range sortedKeys(mergeKeys(w, g)) {
			if !slices.Equal(w[k], g[k]) {
				if nerr++; nerr > 5 {
					t.Errorf("%s: ...", name)
					break
				}
				t.Errorf("%s %s:\n\tgenerated: %v\n\tparsed:    %v", name, k, w[k], g[k])
			}
		}
	}
	t.Logf("%s: %d rules in %d sets", ssaDir, nrules, len(c.Sets))
}

func mergeKeys[V any](a, b map[string]V) map[string]bool {
	m := make(map[string]bool)
	for k := range a {
		m[k] = true
	}
	for k := range b {
		m[k] = true
	}
	return m
}

func sortedKeys[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	return keys
}

func genDirParent(dir string, err error) (string, error) {
	return filepath.Dir(dir), err
}
