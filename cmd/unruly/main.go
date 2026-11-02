// Unruly runs static analyzers over the Go compiler's SSA rewrite rules.
//
// Usage:
//
//	unruly [flags] [path]
//
// Path is a Go root or an SSA _gen directory; it defaults to `go env GOROOT`.
// With -rev, path must be a Go git repository, and unruly analyzes the given
// revision instead of the working tree.
//
// Unruly prints one line per finding, "file:line: analyzer: message".
// It exits with status 1 if there are findings, and 2 if there are errors,
// including rules that fail to parse.
package main

import (
	"flag"
	"fmt"
	"os"
	"os/exec"
	"regexp"
	"slices"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers"
	"github.com/josharian/unruly/internal/gitrev"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
)

var (
	runFlag  = flag.String("run", "", "run only analyzers whose names match this `regexp`")
	archFlag = flag.String("arch", "", "comma-separated `list` of arches (all their rule sets) or rule sets (e.g. AMD64latelower) to analyze")
	revFlag  = flag.String("rev", "", "analyze this `revision` of the Go git repository at path")
	listFlag = flag.Bool("list", false, "list analyzers and exit")
)

func main() {
	flag.Usage = func() {
		fmt.Fprintf(os.Stderr, "usage: unruly [flags] [goroot | _gen dir | git repo with -rev]\n")
		flag.PrintDefaults()
	}
	flag.Parse()
	os.Exit(run())
}

func run() int {
	selected, err := selectAnalyzers(*runFlag)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	if *listFlag {
		for _, a := range selected {
			doc, _, _ := strings.Cut(a.Doc, "\n")
			fmt.Printf("%-16s %s\n", a.Name, doc)
		}
		return 0
	}
	if flag.NArg() > 1 {
		flag.Usage()
		return 2
	}

	path := flag.Arg(0)
	if path == "" {
		out, err := exec.Command("go", "env", "GOROOT").Output()
		if err != nil {
			fmt.Fprintf(os.Stderr, "go env GOROOT: %v\n", err)
			return 2
		}
		path = strings.TrimSpace(string(out))
	}
	if *revFlag != "" {
		path, err = gitrev.GenDir(path, *revFlag)
	} else {
		path, err = ops.FindGenDir(path)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}

	c, err := rules.Load(path)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	status := 0
	for _, err := range c.Errors {
		fmt.Fprintln(os.Stderr, err)
		status = 2
	}
	sets, err := selectSets(c, *archFlag)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}

	diags, err := analysis.Run(c, sets, selected)
	for _, d := range diags {
		fmt.Println(d)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	if status == 0 && len(diags) > 0 {
		status = 1
	}
	return status
}

func selectAnalyzers(pattern string) ([]*analysis.Analyzer, error) {
	if pattern == "" {
		return analyzers.All(), nil
	}
	rx, err := regexp.Compile(pattern)
	if err != nil {
		return nil, err
	}
	var sel []*analysis.Analyzer
	for _, a := range analyzers.All() {
		if rx.MatchString(a.Name) {
			sel = append(sel, a)
		}
	}
	if len(sel) == 0 {
		return nil, fmt.Errorf("no analyzers match %q", pattern)
	}
	return sel, nil
}

func selectSets(c *rules.Corpus, list string) ([]*rules.RuleSet, error) {
	if list == "" {
		return c.Sets, nil
	}
	var sets []*rules.RuleSet
	for _, name := range strings.Split(list, ",") {
		n := len(sets)
		for _, s := range c.Sets {
			if (s.Name() == name || s.Arch.Name == name) && !slices.Contains(sets, s) {
				sets = append(sets, s)
			}
		}
		if len(sets) == n {
			return nil, fmt.Errorf("no rule sets named %q", name)
		}
	}
	return sets, nil
}
