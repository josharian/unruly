package loweringcoverage

import (
	"strconv"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/rules"
)

// checkRemat reports address computations that lower to ops that are not
// rematerializeable.
//
// The address of a variable (Addr, LocalAddr) and of an outgoing argument
// slot (OffPtr of SP) must lower to an op that regalloc rematerializes
// rather than spills. A spilled address of an outgoing argument slot lets
// GC scan a callee's uninitialized result (golang.org/issue/42944).
// Liveness must also see the address op as a use of its variable.
func checkRemat(pass *analysis.Pass, ai *archInfo, sets []*matcher) {
	g := pass.Ops.Generic
	lower := sets[0].set
	n := typNames(ai.ptrSize)
	bp := n["BytePtr"]
	sp := &term{op: g.Op("SP"), typ: n["Uintptr"]}
	sb := &term{op: g.Op("SB"), typ: n["Uintptr"]}
	sym := val{k: vSym}

	type check struct {
		op   string
		t    *term
		addr bool // must be seen by liveness as a use of its symbol
	}
	// What goes wrong when the address is spilled.
	spill := map[string]string{
		"OffPtr": "a spilled pointer into the outgoing args area makes GC treat a callee's possibly uninitialized argument or result slot as live (golang.org/issue/42944)",
		"Addr":   "uses of the reloaded address don't mention the variable, so liveness can consider it dead too early (golang.org/issue/15365)",
	}
	spill["LocalAddr"] = spill["Addr"]
	var checks []check
	if op := g.Op("OffPtr"); op != nil {
		checks = append(checks, check{"OffPtr", &term{op: op, typ: bp, auxint: intVal(8), aux: val{k: vNil}, args: []*term{sp}}, false})
	}
	if op := g.Op("Addr"); op != nil {
		checks = append(checks, check{"Addr", &term{op: op, typ: bp, auxint: intVal(0), aux: sym, args: []*term{sb}}, true})
	}
	if op := g.Op("LocalAddr"); op != nil && op.ArgLength == 2 {
		for _, ptrs := range []tri{yes, no} {
			elem := &typ{name: "T", kind: tStruct, size: 16, align: 8, ptrs: ptrs}
			mem := memTerm(g)
			checks = append(checks, check{"LocalAddr", &term{op: op, typ: ptrTo(elem, ai.ptrSize), auxint: intVal(0), aux: sym, args: []*term{sp, mem}}, true})
		}
	}
	reported := map[string]bool{}
	for _, c := range checks {
		rs := lower.ByOp[c.t.op]
		if len(rs) == 0 || reported[c.op] {
			continue
		}
		// Report only if every possible lowering is bad.
		outs := rewrite(c.t, sets)
		if len(outs) == 0 {
			continue
		}
		var res *term
		var why string
		for _, out := range outs {
			if out.op == nil || out.op.IsGeneric() {
				why = ""
				break
			}
			w := ""
			switch {
			case !out.op.Rematerializeable:
				w = "is not rematerializeable: regalloc may spill the address, and " + spill[c.op]
			case c.addr && !usesSym(out.op.SymEffect):
				// liveness/plive.go: valueEffects counts an op as a use of
				// its symbol only if its symEffect has Read or Addr.
				w = "has symEffect " + strconv.Quote(out.op.SymEffect) + ", so liveness does not see it use the variable and may consider the variable dead while its address is live"
			}
			if w == "" {
				why = ""
				break
			}
			// Show the last outcome, which follows only the rules
			// known to apply.
			res, why = out, w
		}
		if why == "" {
			continue
		}
		reported[c.op] = true
		pass.Reportf(rulePos(rs), "%s lowers to %s, which %s", c.t, res, why)
	}
}

// usesSym reports whether liveness counts an op with symEffect e as a use
// of its symbol: liveness/plive.go valueEffects tests SymRead|SymAddr,
// which the effects Read, RdWr, and Addr include.
func usesSym(e string) bool {
	for _, f := range strings.Split(e, ",") {
		switch strings.TrimSpace(f) {
		case "Read", "RdWr", "Addr":
			return true
		}
	}
	return false
}

func rulePos(rs []*rules.Rule) rules.Pos { return rs[0].Pos }
