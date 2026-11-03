package analyzers

import "github.com/josharian/unruly/analyzers/simdnames"

func init() { register(simdnames.Analyzer) }
