package analyzers

import "github.com/josharian/unruly/analyzers/loweringcoverage"

func init() { register(loweringcoverage.Analyzer) }
