package analyzers

import "github.com/josharian/unruly/analyzers/condsem"

func init() { register(condsem.Analyzer) }
