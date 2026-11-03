package analyzers

import "github.com/josharian/unruly/analyzers/optablelint"

func init() { register(optablelint.Analyzer) }
