// Package analyzers is the registry of unruly's analyzers.
//
// Each analyzer registers itself in its own file, analyzers/<name>.go:
//
//	package analyzers
//
//	import "github.com/josharian/unruly/analyzers/<name>"
//
//	func init() { register(<name>.Analyzer) }
package analyzers

import (
	"cmp"
	"fmt"
	"slices"

	"github.com/josharian/unruly/analysis"
)

var registry []*analysis.Analyzer

func register(a *analysis.Analyzer) {
	registry = append(registry, a)
}

// All returns every registered analyzer, sorted by name.
func All() []*analysis.Analyzer {
	all := slices.Clone(registry)
	slices.SortFunc(all, func(a, b *analysis.Analyzer) int { return cmp.Compare(a.Name, b.Name) })
	for i := 1; i < len(all); i++ {
		if all[i].Name == all[i-1].Name {
			panic(fmt.Sprintf("two analyzers named %s", all[i].Name))
		}
	}
	return all
}
