// Package loweringcoverage checks that every generic op that can reach an
// arch's lower pass is lowered, and lowered to something sound.
package loweringcoverage

import (
	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

var Analyzer = &analysis.Analyzer{
	Name: "loweringcoverage",
	Doc: `report generic ops that an arch's lowering leaves unlowered or lowers wrongly

After the lower pass, checkLower fails the compilation ("not lowered") if
any generic op other than a few structural ones (Phi, Arg, SP, ...) is
left. This analyzer looks for such gaps, and for lowerings that are
present but wrong, in four ways.

Exhaustiveness. For Load, Store, ZeroSIMD, Zero, Move, and OffPtr, it
evaluates each lowering rule's match and condition over the values that
can reach lowering: every SSA-able scalar type, the SIMD types that the
arch's Load, Store, or ZeroSIMD rules handle, every size and alignment
(and GOAMD64/GOPPC64 setting), and offsets of SP and of other pointers.
Evaluation is three-valued; anything it cannot evaluate counts as a
match. A value that no rule matches crashes the compiler. For example,
PPC64 lowered 8-byte stores with

	(Store {t} ptr val mem) && t.Size() == 8 && (is64BitInt(val.Type) || isPtr(val.Type))

so storing a struct{ m map[int]int } matched nothing (issue 45344), and
ARM64 lowered Load and Store of 8-byte SVE predicates but not ZeroSIMD
(issue 81080).

Bytes. For Zero and Move of up to 64 bytes, the stores that a lowering
produces must write exactly bytes [0, s): zeros for Zero, and for Move
the same bytes of the source, all loaded before any store at sizes where
isInlinableMemmove allows the operands to overlap. A rule like

	(Zero [4] {t} ptr mem) && t.Alignment()%2 == 0 => (MOVHstore [6] ptr ... (MOVHstore [0] ptr ... mem))

zeroes 4 bytes past the object. Store and load widths come from the
arch's own Store and Load lowerings.

Reachability. An op that an intrinsic emits on an arch (per
ssagen/intrinsics.go), or that an SSA pass substitutes for an op that
reaches the arch's lowering (prove turns Ctz16 into Ctz16NonZero), needs
a lowering rule. 386 once lowered Ctz16 but not Ctz16NonZero.

Rematerialization. Following the arch's lower and late lower rules,
OffPtr of SP, Addr, and LocalAddr must become rematerializeable ops. A
spilled address of an outgoing argument slot lets GC treat an
uninitialized result as live (issue 42944).`,
	Run: run,
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		if set.Arch.Generic || set.Suffix != "" {
			continue
		}
		ps, ok := ptrSizes[set.Arch.Name]
		if !ok {
			continue
		}
		ai := &archInfo{arch: set.Arch, ptrSize: ps}
		m := newMatcher(ai, set)
		sets := []*matcher{m}
		if late := lateSet(pass.Corpus, set); late != nil {
			sets = append(sets, newMatcher(ai, late))
		}
		checkCoverage(pass, ai, m)
		checkBytes(pass, ai, m, deriveWidths(ai, m, pass.Ops.Generic, simdSizes(set, pass.Ops.Generic)))
		checkRemat(pass, ai, sets)
		checkReach(pass, ai, set)
	}
	return nil
}

func lateSet(c *rules.Corpus, set *rules.RuleSet) *rules.RuleSet {
	for _, s := range c.Sets {
		if s.Arch == set.Arch && s.Suffix == "latelower" {
			return s
		}
	}
	return nil
}
