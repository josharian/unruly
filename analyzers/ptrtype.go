package analyzers

import "github.com/josharian/unruly/analyzers/ptrtype"

func init() { register(ptrtype.Analyzer) }
