package placement

import (
	"strings"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// memInfo says which op arguments are memory states.
//
// For generic ops, opsig says. Arch op tables don't: a memory argument
// has an empty register mask, like a flags argument, and many loads
// (such as ARM64's MOVDloadidx) have neither a symEffect nor a Mem type.
// So memInfo infers arch ops' memory arguments from the rules themselves:
// a variable that occupies a memory argument anywhere in a rule is a
// memory state everywhere in that rule. Lowering rules such as
// (Load ptr mem) => (MOVQload ptr mem) seed the arch ops, and rules
// such as (MOVDload [off] {sym} (ADD ptr idx) mem) => (MOVDloadidx ptr idx mem)
// carry the fact to ops that no lowering rule produces.
type memInfo struct {
	args     map[*ops.Op]map[int]bool // arch op argument indexes; lastArg for a variadic op's last
	produces map[*ops.Op]bool         // arch ops seen producing a memory state
}

const lastArg = -1

func inferMem(c *rules.Corpus) *memInfo {
	m := &memInfo{args: make(map[*ops.Op]map[int]bool), produces: make(map[*ops.Op]bool)}
	// An op that reads or writes a symbol's memory takes a memory
	// state, and check.go requires memory to be the last argument.
	for _, a := range c.Ops.Archs {
		for _, op := range a.Ops {
			switch op.SymEffect {
			case "", "None", "Addr":
				continue
			}
			if i := int(op.ArgLength) - 1; i >= 0 && (i >= len(op.Reg.Inputs) || op.Reg.Inputs[i].Empty()) {
				m.args[op] = map[int]bool{i: true}
			}
		}
	}
	for changed := true; changed; {
		changed = false
		for _, s := range c.Sets {
			for _, r := range s.Rules {
				if m.learn(r) {
					changed = true
				}
			}
		}
	}
	return m
}

// An occurrence is a variable in a rule: a match binding, a match leaf,
// or a result leaf. Parent is nil for a top-level value.
type occurrence struct {
	name   string
	node   *rules.Value // the node itself (compound for a match binding)
	parent *rules.Value
	index  int // in parent.Args
}

// occurrences returns the occurrences of match-bound variables in r.
func occurrences(r *rules.Rule) []occurrence {
	bound := make(map[string]bool)
	var occs []occurrence
	var walk func(v, parent *rules.Value, i int, match bool)
	walk = func(v, parent *rules.Value, i int, match bool) {
		if v.Name != "" && (match && rules.IsVarText(v.Name) || !match && v.IsVar() && bound[v.Name]) {
			bound[v.Name] = true
			occs = append(occs, occurrence{v.Name, v, parent, i})
		}
		for j, a := range v.Args {
			walk(a, v, j, match)
		}
	}
	for _, v := range r.MatchValues() {
		walk(v, nil, 0, true)
	}
	for _, v := range r.ResultValues() {
		walk(v, nil, 0, false)
	}
	return occs
}

// learn records the memory facts r implies and reports whether any are new.
func (m *memInfo) learn(r *rules.Rule) bool {
	changed := false
	markArg := func(op *ops.Op, k int) {
		if op.IsGeneric() || m.args[op][k] {
			return
		}
		if m.args[op] == nil {
			m.args[op] = make(map[int]bool)
		}
		m.args[op][k] = true
		changed = true
	}
	markProduces := func(op *ops.Op) {
		if !op.IsGeneric() && !m.produces[op] {
			m.produces[op] = true
			changed = true
		}
	}

	// The result of a value rule replaces its match.
	if !r.IsBlock() && r.Result != nil && !r.Result.IsLeaf() {
		if m.producesMem(r.Match.Op) {
			markProduces(r.Result.Op)
		}
		// (Op ...) => (Op2 ...) keeps the args.
		if r.Match.Ellipsis && r.Match.Op.ArgLength >= 0 {
			for i := range int(r.Match.Op.ArgLength) {
				if m.isMemArg(&rules.Value{Op: r.Match.Op, Args: make([]*rules.Value, r.Match.Op.ArgLength)}, i) {
					markArg(r.Result.Op, i)
				}
			}
		}
	}

	occs := occurrences(r)
	isMem := make(map[string]bool)
	for _, o := range occs {
		if o.parent != nil && m.isMemArg(o.parent, o.index) || !o.node.IsLeaf() && m.producesMem(o.node.Op) {
			isMem[o.name] = true
		}
	}
	for _, o := range occs {
		if !isMem[o.name] {
			continue
		}
		if !o.node.IsLeaf() {
			markProduces(o.node.Op)
		}
		if o.parent == nil {
			continue
		}
		if k, ok := argKey(o.parent, o.index); ok {
			markArg(o.parent.Op, k)
		}
	}
	return changed
}

// argKey returns the key of v.Args[i] in memInfo.args.
func argKey(v *rules.Value, i int) (int, bool) {
	if v.Op.ArgLength >= 0 {
		return i, true
	}
	if v.Rest || i != len(v.Args)-1 {
		return 0, false
	}
	return lastArg, true
}

// isMemArg reports whether v.Args[i] is a memory state.
func (m *memInfo) isMemArg(v *rules.Value, i int) bool {
	op := v.Op
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		switch {
		case !ok:
			return false
		case sig.Variadic != nil:
			// Calls take memory last.
			return sig.Result.Kind == opsig.Results && !v.Rest && i == len(v.Args)-1
		}
		return i < len(sig.Args) && sig.Args[i].Kind == opsig.Mem
	}
	k, ok := argKey(v, i)
	return ok && m.args[op][k]
}

// producesMem reports whether op's result is a memory state.
func (m *memInfo) producesMem(op *ops.Op) bool {
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		return ok && sig.Result.Kind == opsig.Mem
	}
	return op.Typ == "Mem" || m.produces[op]
}

// carriesMem reports whether op's result is or contains a memory state
// (as a tuple or a call's results do). A load's result does not.
func (m *memInfo) carriesMem(op *ops.Op) bool {
	if m.producesMem(op) {
		return true
	}
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		if !ok {
			return false
		}
		switch sig.Result.Kind {
		case opsig.Results:
			return true
		case opsig.Tuple:
			for _, e := range sig.Result.Elems {
				if e.Kind == opsig.Mem {
					return true
				}
			}
		}
		return false
	}
	// Arch ops often have no default type. An op that writes memory
	// produces a memory state, alone or in a tuple.
	return strings.Contains(op.Typ, "Mem") || op.Call || op.TailCall || op.HasSideEffects ||
		strings.Contains(op.SymEffect, "Write") || strings.Contains(op.SymEffect, "RdWr")
}

// readsMem reports whether v, a match or result node, has a memory argument.
func (m *memInfo) readsMem(v *rules.Value) bool {
	for i := range v.Args {
		if m.isMemArg(v, i) {
			return true
		}
	}
	return false
}
