package rules

import (
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"

	"github.com/josharian/unruly/ops"
)

// RuleSet is the input to one rulegen invocation: the rules files for one
// arch and suffix, which rulegen compiles into a single rewrite function.
//
// Within a RuleSet, rules for the same op (or block kind) are tried in
// order, and the first that matches wins. Different RuleSets are different
// passes; for example, AMD64latelower rules run after all AMD64 rules.
type RuleSet struct {
	Arch   *ops.Arch
	Suffix string  // "", "splitload", or "latelower"
	Files  []*File // in rulegen order, e.g. AMD64.rules then simdAMD64.rules
	Rules  []*Rule // the rules of Files, in order

	// ByOp and ByBlock group value rules by match op and
	// block rules by match block kind, each in order.
	ByOp    map[*ops.Op][]*Rule
	ByBlock map[*ops.Block][]*Rule
}

// Name returns the set's name, such as "AMD64" or "AMD64latelower".
func (s *RuleSet) Name() string { return s.Arch.Name + s.Suffix }

func (s *RuleSet) String() string { return s.Name() }

// Corpus is all the rules of one _gen directory (or test directory),
// parsed and resolved against op tables.
type Corpus struct {
	Ops    *ops.Tables
	Sets   []*RuleSet // sorted by name
	Errors []error    // parse errors and unrecognized files
}

// Suffixes are the rule file suffixes, each a separate rewrite pass.
var Suffixes = []string{"", "splitload", "latelower"}

// SetFiles returns the base names of the rules files rulegen reads for
// arch and suffix, in order. Not all need exist.
func SetFiles(arch, suffix string) []string {
	names := []string{arch + suffix + ".rules"}
	if suffix == "" {
		names = append(names, "simd"+arch+".rules")
		if arch == "ARM64" {
			// SVE shares the ARM64 backend.
			names = append(names, "simdARM64SVE.rules")
		}
	}
	return names
}

// Load loads the op tables and rules of path, which may be a Go root or a
// _gen directory.
func Load(path string) (*Corpus, error) {
	dir, err := ops.FindGenDir(path)
	if err != nil {
		return nil, err
	}
	tables, err := ops.Load(dir)
	if err != nil {
		return nil, err
	}
	return LoadDir(dir, tables)
}

// LoadDir parses the *.rules files in dir using tables.
// The files need not be in tables' _gen directory.
func LoadDir(dir string, tables *ops.Tables) (*Corpus, error) {
	paths, err := filepath.Glob(filepath.Join(dir, "*.rules"))
	if err != nil {
		return nil, err
	}
	files := make(map[string][]byte)
	for _, p := range paths {
		b, err := os.ReadFile(p)
		if err != nil {
			return nil, err
		}
		files[p] = b
	}
	return Parse(tables, files), nil
}

// Parse parses the given rules files, keyed by path. Each file's base name
// determines its rule set, as in a _gen directory: generic.rules,
// AMD64latelower.rules, simdAMD64.rules, and so on.
func Parse(tables *ops.Tables, files map[string][]byte) *Corpus {
	c := &Corpus{Ops: tables}
	byBase := make(map[string]string)
	for p := range files {
		byBase[filepath.Base(p)] = p
	}
	used := make(map[string]bool)
	for _, a := range tables.Archs {
		for _, suffix := range Suffixes {
			set := &RuleSet{Arch: a, Suffix: suffix}
			for _, base := range SetFiles(a.Name, suffix) {
				p, ok := byBase[base]
				if !ok {
					continue
				}
				used[base] = true
				f, errs := ParseFile(p, files[p], a)
				c.Errors = append(c.Errors, errs...)
				set.Files = append(set.Files, f)
			}
			if len(set.Files) > 0 {
				c.Errors = append(c.Errors, set.index()...)
				c.Sets = append(c.Sets, set)
			}
		}
	}
	for base, p := range byBase {
		if !used[base] {
			c.Errors = append(c.Errors, fmt.Errorf("%s: rules file does not belong to any arch", p))
		}
	}
	slices.SortFunc(c.Sets, func(a, b *RuleSet) int { return strings.Compare(a.Name(), b.Name()) })
	slices.SortFunc(c.Errors, func(a, b error) int { return strings.Compare(a.Error(), b.Error()) })
	return c
}

// Set returns the rule set with the given name (see RuleSet.Name), or nil.
func (c *Corpus) Set(name string) *RuleSet {
	for _, s := range c.Sets {
		if s.Name() == name {
			return s
		}
	}
	return nil
}

// index fills in s.Rules, s.ByOp, and s.ByBlock and checks the
// properties rulegen enforces across the rules for one op.
func (s *RuleSet) index() []error {
	s.ByOp = make(map[*ops.Op][]*Rule)
	s.ByBlock = make(map[*ops.Block][]*Rule)
	for _, f := range s.Files {
		for _, r := range f.Rules {
			r.Set = s
			s.Rules = append(s.Rules, r)
			if r.IsBlock() {
				s.ByBlock[r.MatchBlock.Info] = append(s.ByBlock[r.MatchBlock.Info], r)
			} else {
				s.ByOp[r.Match.Op] = append(s.ByOp[r.Match.Op], r)
			}
		}
	}
	var errs []error
	for _, rules := range s.ByOp {
		for i, r := range rules {
			if r.Match.Ellipsis && len(rules) > 1 {
				errs = append(errs, &Error{r.Pos, "found ellipsis in rule, but there are other rules with the same op"})
			}
			if i+1 < len(rules) && r.Unconditional() {
				errs = append(errs, &Error{rules[i+1].Pos, fmt.Sprintf("rule follows unconditional rule %s at %s", r.MatchText, r.Pos)})
			}
		}
	}
	return errs
}
