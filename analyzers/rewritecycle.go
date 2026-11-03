package analyzers

import "github.com/josharian/unruly/analyzers/rewritecycle"

func init() { register(rewritecycle.Analyzer) }
