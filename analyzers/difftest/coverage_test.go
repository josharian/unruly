package difftest

import (
	"fmt"
	"os"
	"regexp"
	"sort"
	"strings"
	"testing"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analysis/analysistest"
	"github.com/josharian/unruly/internal/gensem"
	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/rules"
)

// TestCoverage logs how many rules difftest exercises on the test tree,
// and why it skips the others:
//
//	UNRULY_COVERAGE=1 go test -v -run Coverage ./analyzers/difftest
//
// UNRULY_COVERAGE=unsat also lists the rules that no generated input
// satisfied, and UNRULY_COVERAGE=stop the rules difftest gave up on.
func TestCoverage(t *testing.T) {
	mode := os.Getenv("UNRULY_COVERAGE")
	if mode == "" {
		t.Skip("set UNRULY_COVERAGE")
	}
	reasons := map[string]int{}
	var tested, unsat, total int
	digits := regexp.MustCompile(`\d+`)
	trace = func(r *rules.Rule, sat int, stop error) {
		total++
		switch {
		case stop != nil:
			reasons[digits.ReplaceAllString(stop.Error(), "N")]++
			if mode == "stop" {
				fmt.Printf("STOP %s: %v: %s\n", r.Pos, stop, r.Text)
			}
		case sat == 0:
			unsat++
			if mode == "unsat" {
				fmt.Printf("UNSAT %s: %s\n", r.Pos, r.Text)
			}
		default:
			tested++
		}
	}
	defer func() { trace = nil }()
	analysistest.Survey(t, Analyzer)
	t.Logf("%d generic-only rules: %d tested, %d never satisfied", total, tested, unsat)
	type kv struct {
		k string
		v int
	}
	var kvs []kv
	for k, v := range reasons {
		kvs = append(kvs, kv{k, v})
	}
	sort.Slice(kvs, func(i, j int) bool { return kvs[i].v > kvs[j].v })
	for _, e := range kvs {
		t.Logf("%5d %s", e.v, e.k)
	}
}

// TestTrace prints why difftest rejects the inputs it generates for the
// rule at $UNRULY_RULE (such as generic.rules:611), and its finding.
func TestTrace(t *testing.T) {
	want := os.Getenv("UNRULY_RULE")
	if want == "" {
		t.Skip("set UNRULY_RULE=file:line")
	}
	c, err := rules.Load(testenv.GenDir(t))
	if err != nil {
		t.Fatal(err)
	}
	pass := &analysis.Pass{Analyzer: Analyzer, Corpus: c, Ops: c.Ops, Sets: c.Sets}
	tt := &tester{pass: pass, matchers: map[*gensem.Config]*gensem.Matcher{}}
	n := 0
	traceReject = func(why, lhs string) {
		if n++; n <= 30 {
			fmt.Println(why, lhs)
		}
	}
	defer func() { traceReject = nil }()
	for _, s := range c.Sets {
		for _, r := range s.Rules {
			if !strings.HasSuffix(r.Pos.String(), "/"+want) {
				continue
			}
			for _, cfg := range gensem.ArchConfigs(s.Arch.Name) {
				tt.matchers[cfg] = gensem.NewMatcher(cfg)
			}
			f, sat, stop := tt.check1(r)
			fmt.Printf("%s: %d inputs matched; stopped: %v\n", r.Text, sat, stop)
			if f != nil {
				fmt.Println(f.msg)
			}
		}
	}
}
