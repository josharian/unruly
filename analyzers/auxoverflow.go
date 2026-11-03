package analyzers

import "github.com/josharian/unruly/analyzers/auxoverflow"

func init() { register(auxoverflow.Analyzer) }
