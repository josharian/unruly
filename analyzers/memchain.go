package analyzers

import "github.com/josharian/unruly/analyzers/memchain"

func init() { register(memchain.Analyzer) }
