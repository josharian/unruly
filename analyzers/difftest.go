package analyzers

import "github.com/josharian/unruly/analyzers/difftest"

func init() { register(difftest.Analyzer) }
