package analyzers

import "github.com/josharian/unruly/analyzers/selfrewrite"

func init() { register(selfrewrite.Analyzer) }
