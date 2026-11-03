package analyzers

import "github.com/josharian/unruly/analyzers/rulelint"

func init() { register(rulelint.Analyzer) }
