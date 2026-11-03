package analyzers

import "github.com/josharian/unruly/analyzers/divzero"

func init() { register(divzero.Analyzer) }
