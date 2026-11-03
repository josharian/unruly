package analyzers

import "github.com/josharian/unruly/analyzers/simdcodegen"

func init() { register(simdcodegen.Analyzer) }
