# unruly

Static analyzers for the Go compiler's SSA rewrite rules
(`src/cmd/compile/internal/ssa/_gen/*.rules`).

```
go run ./cmd/unruly                     # analyze `go env GOROOT`
go run ./cmd/unruly ~/go/tip            # a Go root, or a _gen directory
go run ./cmd/unruly -run dupmatch -arch AMD64,generic ~/go/tip
go run ./cmd/unruly -rev go1.22.0 ~/go/tip   # a revision of a Go git repo
go run ./cmd/unruly -list
```

Output is `file:line: analyzer: message`. Exit status is 1 if there are
findings and 2 if there are errors (including rules that fail to parse).

## Layout

| Package | Contents |
| --- | --- |
| `ops` | Op and block tables, loaded from a _gen directory |
| `opsig` | Operand kinds, widths, and signedness of generic ops |
| `rules` | Rules parser, AST, and helpers for rulegen's semantics |
| `typecheck` | Go types for the Go expressions in rules |
| `internal/facts` | Integer ranges of rule expressions, from conditions |
| `analysis` | `Analyzer`, `Pass`, `Run` |
| `analysis/analysistest` | Test harness |
| `analyzers` | The registry, `analyzers.All()` |
| `analyzers/<name>` | One analyzer each |
| `cmd/unruly` | The driver |

## Writing an analyzer

1. Create `analyzers/<name>/<name>.go` declaring
   `var Analyzer = &analysis.Analyzer{Name: "<name>", Doc: "...", Run: run}`.
   `Run` receives a `*analysis.Pass` and reports with
   `pass.Reportf(rule.Pos, ...)`.
2. Register it in a new file, `analyzers/<name>.go`:
   ```go
   package analyzers

   import "github.com/josharian/unruly/analyzers/<name>"

   func init() { register(<name>.Analyzer) }
   ```
3. Add `analyzers/<name>/testdata/*.rules` and a test (see below).

See `analyzers/dupmatch` and `analyzers/selfrewrite` for examples.

A `Pass` has `Sets`, the rule sets to analyze (`-arch` selects them), and
`Corpus`, everything loaded, for analyses that relate rule sets (such as
whether every generic op that `generic.rules` produces is lowered on
every arch). `pass.Rules()` iterates over the rules of `Sets`.

## The AST

A `rules.Corpus` holds the op tables (`Ops`) and one `RuleSet` per rulegen
invocation: an arch and a suffix (`""`, `"splitload"`, or `"latelower"`). A
rule set's `Files` are read in order (`AMD64.rules`, then `simdAMD64.rules`;
for ARM64 also `simdARM64SVE.rules`), and its `Rules` are in that order. For
each op, the first matching rule wins, so order matters only within the
op's group: `ByOp[op]` and `ByBlock[block]`. Different rule sets are
different passes; `generic`, `dec`, `dec64`, `divmod`, and `divisible` are
"arches" whose rules rewrite generic ops.

Each `rules.Rule` is one `|` expansion of a source rule (`Orig`; expansions
share `Pos` and are numbered by `Alt` out of `NumAlts`). `Pos` is the rule's
first line. A value rule has `Match` and a `Result` (or `ResultCode`, the
code of a `{...}` result, and possibly `Placement`, the `x.Block` of `@x.Block`).
A block rule has `MatchBlock` and `ResultBlock`, each with `Info` (an
`*ops.Block`), `Controls`, and `Succs`. `Cond` is the raw condition and
`CondExpr` its `go/ast` parse.

A `rules.Value` is a compound s-expression (`Op` is the resolved `*ops.Op`)
or a leaf (`Op == nil`):

```
x:(MOVQload <t> [off] {sym} ptr mem)
Name  OpName  Type AuxInt Aux   Args
```

`Name` is the binding name; for a leaf it is the leaf's text. Match leaves
are variables or `_`. Result leaves are arbitrary Go expressions, such as
`x.Args[0]`. `Ellipsis` marks `(Op ...)` and `Rest` a trailing `___`.

## rulegen semantics to know

The parser rejects everything rulegen rejects, but rules can still mean
something other than they appear to. Helpers in `rules` encode these:

- **Repeated names are equality constraints.** `(Sub64 x x)` matches only
  if both args are the same `*Value` (pointer equality, so it depends on
  CSE). This applies across kinds too: in `(Load <t> p (Store {t} p x _))`,
  the load's type must equal the store's aux. See `Rule.MatchOccurrences`,
  `Rule.MatchVars`.
- **Non-variable `<>`, `[]`, `{}` in a match are comparisons.** `[0]`,
  `{nil}`, and `<typ.UInt64>` compare against that Go expression; `[c]`
  binds `c`. See `IsVarText`.
- **Commutative ops match both orders** of their first two args, trying the
  written order first; the condition is checked for each order, and the
  first success binds the variables. Nested commutative ops multiply. See
  `Value.Commutes`, `Commutations`.
- **Result types.** A top-level result without `<type>` keeps the rewritten
  value's type, *not* the op's default type, unless the result has `@block`
  placement, in which case it gets the op's default type like any
  sub-expression. Sub-expressions need an explicit type or an op default.
  A top-level leaf result (`=> x`) makes `v` a copy of `x` but keeps
  `v`'s type. See `Rule.ResultType`, `ops.TypeExpr`.
- **Results reset aux fields.** A non-ellipsis result zeros `AuxInt` and
  `Aux` unless it sets them. An ellipsis rule `(Op ...) => (Op2 ...)` only
  changes the op, keeping type, aux, auxint, and args; it must be the only
  rule for `Op`.
- **Identical result sub-expressions are shared:** a value rule's result
  creates one value for textually identical sub-expressions.
- **Aux types** come from the op: `Op.AuxType`/`Op.AuxIntType` are the Go
  types rulegen converts through (e.g. `[c]` on `MOVQload` is an `int32`),
  as computed by that revision's own rulegen.
- **Value vs. block rules** are distinguished by whether the first op name is
  a block kind (generic blocks first). Generic ops are resolved before arch
  ops; ops also resolve by argument count. See `Arch.ResolveOp`.
- **Syntax quirks:** `//` starts a comment anywhere, even in a Go string.
  A rule ends at the first line where its text contains `=>`, doesn't end with
  `=>`, and has balanced parentheses. `|` alternations expand everywhere
  except inside `[...]` and conditions.
- Within a block rule, `<type>` is ignored, and successors may only be kept
  or swapped. Variables `v`, `b`, `config`, `typ`, and `fe` are predefined
  in conditions and results (`Tables.ReservedNames`).
- `_` in a match's `<>`, `[]`, or `{}` is a wildcard, like a leaf `_`.
- `Rule.Unconditional` reports whether a rule applies to every value of its
  op. rulegen rejects rules after an unconditional one.

## Op tables

`ops.Load(genDir)` builds the _gen package of that Go tree with a generated
`main` that dumps rulegen's registered tables by reflection, so the tables are
exactly what that tree's rulegen sees, for any revision back to 2020. The
first load of a tree takes a few seconds; results are cached in the user
cache directory, keyed by the _gen Go sources.

```go
t.Arch("AMD64").Op("ADDQ")          // arch-specific op
t.Arch("AMD64").LookupOp("Add64")   // generic first, then arch, as in rules
t.Generic                           // the generic ops and blocks
op.ArgLength, op.Commutative, op.Typ, op.Aux, op.AuxIntType, op.Reg.Inputs[0], ...
a.Classify(op.Reg.Inputs[0])        // ops.RegGP, RegFP|RegSIMD, RegOther, ...
a.FormatRegMask(m)                  // "AX CX DX ..."
```

Fields not modeled are in `Op.Raw`/`Arch.Raw`. Register classes overlap
(on AMD64 and ARM64 the FP and SIMD masks coincide); memory and flags
arguments have empty masks.

## Typed expressions

`typecheck.Check(set)` type-checks the Go expressions in a rule set's rules
against the real declarations in the Go tree (helpers in rewrite.go,
`config` fields, `math/bits`, ...), as rulegen's generated code would use
them. It declares each match variable as that generated code does: a value
variable is a `*ssa.Value`, `<t>` a `*types.Type`, `[c]` on `MOVLload` an
`int32` (via `auxIntToInt32`), `{sym}` an `ssa.Sym`. Results are cached per
rule set; the first check of a tree takes about a second.

```go
res, err := typecheck.Check(rule.Set)
tr := res.Rule(rule)
tr.Vars["c"].Type()                                        // int64
res.Info.TypeOf(tr.Cond)                                   // bool
res.Info.TypeOf(tr.Expr(rule.Result, typecheck.AuxInt))    // int32: the result's [int32(c)]
res.Info.Types[tr.Expr(v, typecheck.AuxInt)].Value         // constant value, if any
tr.Errors                                                  // e.g. "constant 300 overflows int8"
```

In the context rulegen gives it, an untyped constant has its converted type
(`[-1]` on a `Const8` result is an `int8`). Expressions come from
generated source, so their positions are not in the rules file. Checking
needs the tree's source and its rulegen output; it works on `go env
GOROOT`-style trees and on revisions extracted by the test harness.

## Integer facts

`facts.New(res, rule)` derives what is known about a rule's integer
expressions when it fires, from its variables' types and its condition,
and answers queries about any integer expression of the rule (from
`typecheck`). It understands comparisons, `&&`, `||`, `!`, conversions,
arithmetic, masks, shifts, `min`/`max`, and `math/bits`; it inlines
helpers like `is32Bit`, `isPowerOfTwo`, `log64u`, and `ValAndOff.Off`
from their definitions in the tree, and bounds helpers that return only
constants, like `MoveSize`. Answers are sound: what it cannot
prove is reported as unknown.

```go
f := facts.New(res, rule)    // for (ADDQconst [c] (ADDQconst [d] x)) && is32Bit(int64(c)+int64(d)) => (ADDQconst [c+d] x)
e := tr.Expr(rule.Result, typecheck.AuxInt)   // c+d
f.Range(e)                   // [-2147483648, 2147483647], ok: its possible values (always within its type)
f.Exact(e)                   // true: no operation in c+d wraps around
f.Overflows(e)               // nil; else each operation or conversion that may wrap, with its true range
f.OverflowsMod(e, 32)        // wraparound that matters modulo 2^32, as for a 32-bit op
f.Fits(c, types.Typ[types.Int8]) // false: c may not fit in int8
f.In(e, 0, 63)               // false: e may not be a valid shift count
f.NonZero(d)                 // false: d may be 0
f.AssumeVar("c", facts.Range(0, 63)) // facts with an op's known auxint domain added
```

`Overflows` treats calls as opaque; to check `ssa.MakeValAndOff(int32(c), off)`,
ask about each argument.

Facts can take more assumptions: `AssumeIn(e, iv)` for an expression,
`ExcludeVar(name, x)`, and `AssumeNot(cond, bind)` for an earlier rule's
condition, which must have been false (`analyzers/auxdomain/prior` derives
these from the rules for the same op). `f.Eval(e, vals)` evaluates an
expression for given variable values, and `f.Holds(vals)` reports whether
they satisfy everything `f` assumes, which turns an unproven bound into a
concrete counterexample (`analyzers/auxdomain/witness` searches for one).

## Generic op signatures

`opsig.Lookup(op)` describes a generic op's arguments and result: kind (Int,
Float, Bool, Ptr, Mem, Tuple, ...), width in bits when the op fixes it, and
signedness when the op implies it. `Rsh32Ux64` takes an unsigned 32-bit value
and an unsigned 64-bit count; `Load`'s result is `Any`, with its width from
the value's type. Ops generated for SIMD are marked `SIMD` and not described.
The table is checked against every generic op of the current tree, so new
ops fail its test until classified. Rules routinely compute narrower-typed
values with wider ops (`(Div16 x y) => (Div32 (SignExt16to32 x) ...)`), so
compare widths with that in mind.

## Testing

```go
func Test(t *testing.T) {
	analysistest.Run(t, "testdata", myanalyzer.Analyzer)
}
```

`testdata` is a miniature _gen directory: file names determine the arch and
rule set (`generic.rules`, `AMD64.rules`, `ARM64latelower.rules`, ...), and
ops resolve against the real op tables. Fixtures must parse cleanly, so
they must be valid rules (sub-expressions typed, no rule after an
unconditional one, ...). Mark expected diagnostics on the rule's first line:

```
(Neg64 (Neg64 y)) => y // want "shadowed by equivalent rule at generic.rules:2"
```

`analysistest.RunFiles` takes fixtures inline instead.

To see an analyzer's findings on the real rules without building
`cmd/unruly` (which breaks while any registered analyzer is mid-edit):

```go
func TestSurvey(t *testing.T) { analysistest.Survey(t, myanalyzer.Analyzer) }
```

and run `go test -v -run Survey ./analyzers/myanalyzer`.
`analysistest.SurveyRevision` does the same for a historical revision.

`analysistest.RunRevision` checks a historical revision, using that
revision's own op tables:

```go
analysistest.RunRevision(t, "79a3482d9e", dupmatch.Analyzer,
	analysistest.Want{File: "PPC64.rules", Line: 557, Message: "shadowed"},
	analysistest.Want{File: "PPC64.rules", Line: 462, Absent: true},
	// Rule matches the source text, before | expansion.
	analysistest.Want{File: "generic.rules", Rule: "(Sub(64|32|16|8) (Add(64|32|16|8) x y) y)"},
)
```

Tests use the Go tree `$UNRULY_GOROOT`, else `~/go/tip`, else
`go env GOROOT`, and the git repository `$UNRULY_GOREPO`, else `~/go/tip`;
they skip if these are missing. A revision's `src` (about 120 MB, without
testdata) is extracted with `git archive` into the user cache directory; the
repository is only read.

## Limitations

- Only typed (`=>`) rules are supported, so revisions before
  79a3482d9e (October 2020) mostly fail to parse.
- Positions are per rule, not per s-expression.
- `CondExpr` positions are relative to the condition text.
