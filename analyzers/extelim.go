package analyzers

import "github.com/josharian/unruly/analyzers/extelim"

func init() { register(extelim.Analyzer) }
