// Package mem classifies SSA ops and rule variables by how they relate to
// memory, and extracts the facts about use counts and pointers that rule
// conditions establish. It is shared by the memchain and memaddr analyzers.
package mem

import (
	"strings"
	"sync"

	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/opsig"
	"github.com/josharian/unruly/rules"
)

// Out says whether and how an op produces a memory state.
type Out uint8

const (
	OutUnknown Out = iota // not yet classified
	OutNone               // a plain value (or flags, or void)
	OutMem                // a memory state
	OutTuple              // a (value, memory) tuple; Select1 is the memory
	OutResults            // call results followed by memory; select with SelectN
)

// OpInfo is how an op relates to memory.
type OpInfo struct {
	// Mem reports that the op's last argument is a memory state.
	Mem bool
	Out Out
	// Read reports whether the op reads memory, when known: from the
	// op's symEffect, or because it is a generic load, Move, or call.
	Read bool
}

// Producer reports whether the op produces a memory state, directly or
// as part of a tuple or call results.
func (i OpInfo) Producer() bool { return i.Out >= OutMem }

// Table classifies the ops of one corpus.
type Table struct {
	info map[*ops.Op]*OpInfo
}

var tables sync.Map // *rules.Corpus -> *Table

// Ops returns the classification of the ops used by c's rules.
//
// The op tables do not say which arguments are memory. Generic ops are
// classified by their signatures (opsig). Arch ops are classified by
// their default type ("Mem", or a tuple with Mem), their symEffect
// (Read, Write), and whether they are calls; arch stores and many other
// memory ops have no default type, so the classification is then
// completed from the rules themselves: a lowering rule's result root has
// the type of its match root, so (Store ...) => (MOVQstore ...) shows
// that MOVQstore produces memory, and an op whose last argument is a
// memory variable takes memory.
func Ops(c *rules.Corpus) *Table {
	if t, ok := tables.Load(c); ok {
		return t.(*Table)
	}
	t := classify(c)
	actual, _ := tables.LoadOrStore(c, t)
	return actual.(*Table)
}

// Op returns the classification of op.
func (t *Table) Op(op *ops.Op) OpInfo {
	if op == nil {
		return OpInfo{}
	}
	i, ok := t.info[op]
	if !ok {
		s := seed(op)
		i = &s
	}
	r := *i
	finish(op, &r)
	return r
}

// finish completes the classification of op once the rules have been
// consulted. Calls that no lowering rule classified return results (and
// memory) through SelectN. An op that takes memory and returns a value or
// a tuple reads memory, whether or not it has a symEffect: PPC64's
// MOVDBRload and ARM64's MOVDloadidx have none.
func finish(op *ops.Op, i *OpInfo) {
	if i.Out == OutUnknown {
		i.Out = OutNone
		if op.Call {
			i.Out = OutResults
		}
	}
	if i.Mem && (i.Out == OutNone || i.Out == OutTuple) {
		i.Read = true
	}
}

func classify(c *rules.Corpus) *Table {
	t := &Table{info: make(map[*ops.Op]*OpInfo)}
	get := func(op *ops.Op) *OpInfo {
		i := t.info[op]
		if i == nil {
			s := seed(op)
			i = &s
			t.info[op] = i
		}
		return i
	}
	for changed := true; changed; {
		changed = false
		for _, s := range c.Sets {
			for _, r := range s.Rules {
				if r.IsBlock() {
					continue
				}
				// The result root has the match root's type.
				if res := r.Result; res != nil && !res.IsLeaf() && !res.Ellipsis {
					if _, src := r.ResultType(res); src == rules.TypeInherited {
						mi, ri := get(r.Match.Op), get(res.Op)
						if ri.Out == OutUnknown && mi.Out != OutUnknown {
							ri.Out = mi.Out
							changed = true
						}
					}
				}
				if r.Match.Ellipsis && r.Result != nil && !r.Result.IsLeaf() {
					mi, ri := get(r.Match.Op), get(r.Result.Op)
					if ri.Out == OutUnknown && mi.Out != OutUnknown {
						ri.Out, ri.Mem = mi.Out, mi.Mem
						changed = true
					}
				}
				// An op whose last argument is a memory variable takes memory.
				vars := memVars(get, r)
				mark := func(v *rules.Value) bool {
					if v.IsLeaf() || len(v.Args) == 0 {
						return true
					}
					last := v.Args[len(v.Args)-1]
					if last.IsVar() && vars[last.Name] && !v.Rest && lastArgUnregistered(v.Op) {
						if i := get(v.Op); !i.Mem {
							i.Mem = true
							changed = true
						}
					}
					return true
				}
				r.Match.Walk(mark)
				if r.Result != nil {
					r.Result.Walk(mark)
				}
			}
		}
	}
	for op, i := range t.info {
		finish(op, i)
	}
	return t
}

// seed classifies op from the op tables alone.
func seed(op *ops.Op) OpInfo {
	var i OpInfo
	if op.IsGeneric() {
		sig, ok := opsig.Lookup(op)
		if !ok || sig.SIMD {
			// Generated SIMD ops: loads and stores are named as such.
			switch {
			case op.Call:
				i = OpInfo{Mem: true, Out: OutResults, Read: true}
			default:
				i.Out = OutNone
			}
			return i
		}
		switch sig.Result.Kind {
		case opsig.Mem:
			i.Out = OutMem
		case opsig.Tuple:
			i.Out = OutNone
			for _, e := range sig.Result.Elems {
				if e.Kind == opsig.Mem {
					i.Out = OutTuple
				}
			}
		case opsig.Results:
			i.Out = OutResults
		default:
			i.Out = OutNone
		}
		if n := len(sig.Args); n > 0 && sig.Args[n-1].Kind == opsig.Mem {
			i.Mem = true
		}
		if op.Call || sig.Variadic != nil && sig.Result.Kind == opsig.Results {
			i.Mem = true
		}
		switch {
		case op.Call:
			i.Read = true
		case i.Mem && i.Out == OutNone:
			i.Read = true // Load, NilCheck, MemEq, AtomicLoad, ...
		case i.Mem:
			i.Read = strings.HasPrefix(op.Name, "Move") || strings.HasPrefix(op.Name, "Atomic")
		}
		return i
	}

	// symEffect is "Read", "Write", "Read,Write", or "RdWr" (an atomic).
	i.Read = strings.Contains(op.SymEffect, "Read") || op.SymEffect == "RdWr"
	write := strings.Contains(op.SymEffect, "Write") || op.SymEffect == "RdWr"
	switch {
	case op.Typ == "Mem":
		i.Out = OutMem
	case strings.HasPrefix(op.Typ, "(") && strings.Contains(op.Typ, "Mem"):
		i.Out = OutTuple
	case op.Typ != "":
		i.Out = OutNone
	case op.Call:
		// Arch calls with a fixed argLength (386's CALLstatic takes
		// only memory) still return their memory through SelectN,
		// like those with variadic arguments; the lowering rule
		// (StaticCall ...) => (CALLstatic ...) classifies them, and
		// finish defaults them to OutResults.
	case write:
		i.Out = OutMem
	case i.Read:
		i.Out = OutNone
	}
	if i.Read || write || op.Call || i.Out >= OutMem {
		i.Mem = op.ArgLength != 0 && lastArgUnregistered(op)
	}
	if op.Call {
		i.Read = true
	}
	return i
}

// memVars returns the variables of r's match that are memory states.
func memVars(get func(*ops.Op) *OpInfo, r *rules.Rule) map[string]bool {
	vars := make(map[string]bool)
	r.Match.Walk(func(v *rules.Value) bool {
		if v.IsLeaf() {
			return false
		}
		i := get(v.Op)
		if i.Mem && len(v.Args) > 0 && !v.Rest {
			if last := v.Args[len(v.Args)-1]; last.IsVar() {
				vars[last.Name] = true
			}
		}
		if v.Name != "" && i.Out == OutMem {
			vars[v.Name] = true
		}
		if v.Name != "" && v.Op.Name == "Select1" && len(v.Args) == 1 && !v.Args[0].IsLeaf() && get(v.Args[0].Op).Out == OutTuple {
			vars[v.Name] = true
		}
		return true
	})
	return vars
}

// lastArgUnregistered reports whether op's last argument, if it has a
// fixed number of arguments, has no register constraint, as memory (and
// flags) arguments don't. It vetoes classifying an op as taking memory
// from its symEffect alone, which some revisions get wrong (S390X
// MOVDaddridx was once marked symEffect "Read").
func lastArgUnregistered(op *ops.Op) bool {
	if op.IsGeneric() || op.ArgLength <= 0 {
		return true
	}
	in := op.Reg.Inputs
	n := int(op.ArgLength)
	return len(in) < n || in[n-1].Empty()
}

// PtrArg returns the index of the argument of op that is the address it
// accesses: the destination of a Move or store, 0 for most ops, and 1 for
// arch ops with a folded load whose first argument is a value, such as
// AMD64's (ADDQload x ptr mem), as faultOnNilArg1 shows.
func PtrArg(op *ops.Op) int {
	if !op.IsGeneric() && op.FaultOnNilArg1 && !op.FaultOnNilArg0 {
		return 1
	}
	return 0
}
