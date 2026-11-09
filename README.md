# unruly

Static analyzers for the Go compiler's SSA rewrite rules
(`src/cmd/compile/internal/ssa/_gen/*.rules`).

Rules are compact and powerful, but weakly typed, and small mistakes
miscompile. unruly reads the rules the way rulegen does, using the op tables
from the same tree, and looks for mistakes like these:

```
MIPS.rules:116: demandedbits: SignExt16to32 (arg 0) reads 16 bits of x, but the match reads only 8 bits (Rsh8x32 (arg 0)): bits 8-15 of x are garbage
AMD64.rules:1621: auxoverflow: dstOff + 8 wraps in int32: its value may be 2147483648, which becomes -2147483648 [...]; MOVQstore's offset is added to a 64-bit address
PPC64.rules:640: rulelint: x.Type.Size() is in bytes [...], so x.Type.Size() <= 16 is always true [...]
```

Each of those was a real bug on tip in early November 2026; the first has
since been fixed upstream.

## Running it

Point it at a Go source tree. There is no default, so you always know which
compiler you're checking.

```
go run ./cmd/unruly ~/go                       # everything
go run ./cmd/unruly -run condsem ~/go          # one analyzer (a regexp)
go run ./cmd/unruly -arch ARM64,generic ~/go   # some arches or rule sets
go run ./cmd/unruly -rev go1.22.0 ~/go         # a past revision (needs a git checkout)
go run ./cmd/unruly -list                      # what's available
```

Output is `file:line: analyzer: message`. The exit status is 0 when clean, 1
when there are findings, and 2 when something went wrong, such as a rule that
fails to parse.

A full run takes about 30 seconds. unruly builds the tree's own `_gen`
package to extract its op tables (cached by content), and type-checks every
rule against the tree's real helpers.

## Testing

```
UNRULY_GOROOT=~/go go test ./...
```

`UNRULY_GOROOT` is required, and it should be a recent git checkout of Go.
Fixtures resolve ops against it, and each analyzer's historical tests check
that it catches a real past bug at the fix's parent commit and stays quiet
at the fix. Those revisions are extracted with `git archive` into your user
cache directory; your checkout is only read.

To see one analyzer's findings while working on it:

```
UNRULY_GOROOT=~/go go test -v -run Survey ./analyzers/condsem
```

[HACKING.md](HACKING.md) covers the internals and how to write an analyzer.

## TODO

- **A baseline.** unruly reports about 390 findings on tip, all real, so
  it can't gate CI yet. Fix them upstream, or add a file of accepted
  findings so that only new ones fail.
- **Arch semantics.** `difftest` randomly tests rules made only of generic
  ops. Teaching its interpreter (`internal/gensem`) arch ops, PPC64 first,
  would cover the lowering rules too.
- **Sibling rules.** Flag a member of a width family (Add8/16/32/64) that
  lacks a condition its siblings have. This was noisy in prototypes.
- **Arch policy.** Table-driven guards: ISA feature checks, SB-relative
  addressing under dynlink, immediate encodability. These tables go stale
  as the assembler changes.
- **Derived pointers.** Zero/Move lowerings that compute a pointer one past
  the end of the object (suspected on S390X, unconfirmed).
- **Pre-2020 trees.** Only typed (`=>`) rules parse, so revisions before
  October 2020 can't be analyzed.
