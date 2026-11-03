package analyzers

import "github.com/josharian/unruly/analyzers/memaddr"

func init() { register(memaddr.Analyzer) }
