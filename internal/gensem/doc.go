// Package gensem interprets SSA rewrite rules on concrete values.
//
// It models enough of the compiler's SSA package to run a rule the way
// rulegen's generated code does: a Value tree with ops, types, and aux
// fields (Value, Type); the semantics of generic ops on concrete bit
// patterns (Interp, GenericOps); the Go expressions in conditions, aux
// fields, and types, including the pure helper functions they call
// (Env); matching a rule against a value (Matcher); building a rule's
// result (Matcher.Build); and generating random values that a rule's
// match might accept (Gen).
//
// Op semantics are a table keyed by op name, so an analyzer of
// arch-specific rules can extend GenericOps with arch ops.
//
// Errors distinguish what the model does not cover (Unsupported), inputs
// outside an op's defined domain (Undefined: the value cannot occur in
// valid SSA), and Go runtime panics in rule expressions (Panic: the
// compiler itself would crash).
package gensem
