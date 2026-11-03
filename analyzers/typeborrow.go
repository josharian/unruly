package analyzers

import "github.com/josharian/unruly/analyzers/typeborrow"

func init() { register(typeborrow.Analyzer) }
