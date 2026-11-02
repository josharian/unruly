// Package analyzers is the registry of all unruly analyzers.
package analyzers

import (
	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/analyzers/dupmatch"
	"github.com/josharian/unruly/analyzers/selfrewrite"
)

// All is every analyzer, sorted by name.
// To register an analyzer, add it here.
var All = []*analysis.Analyzer{
	dupmatch.Analyzer,
	selfrewrite.Analyzer,
}
