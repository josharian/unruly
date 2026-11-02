package analyzers

import "github.com/josharian/unruly/analyzers/dupmatch"

func init() { register(dupmatch.Analyzer) }
