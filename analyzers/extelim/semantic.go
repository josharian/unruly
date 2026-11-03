package extelim

import (
	"fmt"

	"github.com/josharian/unruly/rules"
)

// This file evaluates rules built only from extension ops, AND-with-
// constant ops, and constants, such as
//
//	(MOVBreg (MOVDconst [c])) => (MOVDconst [int64(int8(c))])
//	(Select0 (ANDCCconst [c] (MOVBreg x))) => (Select0 (ANDCCconst [c&0xFF] x))
//
// comparing the match and the result on sample inputs. Such rules fold an
// extension into a constant or a mask, and get the extension's kind or
// width wrong in ways a fact about the result cannot show: dropping a sign
// extension under a mask is right only if the mask clears every bit the
// extension sets.

// semOps gives the semantics of the non-extension ops the evaluator knows,
// per arch: AND with an auxint (andAux, in the whole register, or in the
// low 32 bits with the upper half zeroed for x86's L forms), and
// constants.
type semOp int

const (
	andAux semOp = iota + 1
	andAux32
	constAux
	select0 // Select0 of a tuple op whose first result is the value
)

var semOps = map[string]map[string]semOp{
	"AMD64":   {"ANDLconst": andAux32, "MOVQconst": constAux, "MOVLconst": andAux32},
	"386":     {"ANDLconst": andAux, "MOVLconst": constAux},
	"ARM":     {"ANDconst": andAux, "MOVWconst": constAux},
	"MIPS":    {"ANDconst": andAux, "MOVWconst": constAux},
	"ARM64":   {"ANDconst": andAux, "MOVDconst": constAux},
	"LOONG64": {"ANDconst": andAux, "MOVVconst": constAux},
	"MIPS64":  {"ANDconst": andAux, "MOVVconst": constAux},
	"RISCV64": {"ANDI": andAux, "MOVDconst": constAux},
	// PPC64's ANDconst is andi., which (like the older ANDCCconst) also
	// sets CR0; Select0 of ANDCCconst is its value.
	"PPC64": {"ANDconst": andAux, "ANDCCconst": andAux, "MOVDconst": constAux, "Select0": select0},
	"S390X": {"ANDconst": andAux, "MOVDconst": constAux},
}

// semWorld is an assignment for evaluating a rule: auxint variables in env,
// and leaf variables in leaves.
type semWorld struct {
	env    env
	leaves map[string]uint64
	bound  map[string]*rules.Value // match nodes, by name, for result leaves
}

// semEval evaluates n, reporting false if it cannot.
func (a *archInfo) semEval(n *rules.Value, w semWorld) (uint64, bool) {
	mask := uint64(1)<<a.regBits - 1
	if a.regBits == 64 {
		mask = ^uint64(0)
	}
	if n.Op == nil {
		if v, ok := w.leaves[n.Name]; ok {
			return v & mask, true
		}
		if m := w.bound[n.Name]; m != nil {
			return a.semEval(m, w)
		}
		return 0, false
	}
	if e, ok := a.exts[n.Op.Name]; ok && len(n.Args) == 1 {
		x, ok := a.semEval(n.Args[0], w)
		return uint64(applyExt(int64(x), e)) & mask, ok
	}
	if a.moves[n.Op.Name] && len(n.Args) == 1 {
		return a.semEval(n.Args[0], w)
	}
	op := semOps[n.Op.Arch.Name][n.Op.Name]
	if n.Op.IsGeneric() && n.Op.Name == "Select0" {
		op = semOps[a.name]["Select0"]
	}
	var aux val
	switch {
	case n.AuxInt == "":
	case rules.IsVarText(n.AuxInt):
		aux = w.env[n.AuxInt]
	default:
		aux = evalString(n.AuxInt, w.env)
	}
	switch op {
	case select0:
		if len(n.Args) != 1 || n.Args[0].Op == nil || semOps[a.name][n.Args[0].Op.Name] != andAux {
			return 0, false
		}
		return a.semEval(n.Args[0], w)
	case constAux:
		if !aux.k.isInt() || len(n.Args) != 0 {
			return 0, false
		}
		return uint64(aux.i) & mask, true
	case andAux, andAux32:
		if !aux.k.isInt() || len(n.Args) != 1 {
			return 0, false
		}
		x, ok := a.semEval(n.Args[0], w)
		r := x & uint64(aux.i)
		if op == andAux32 {
			r = uint64(uint32(r))
		}
		return r & mask, ok
	}
	return 0, false
}

// semEvaluable reports whether the evaluator knows every op of v.
func (a *archInfo) semEvaluable(v *rules.Value) bool {
	ok := true
	v.Walk(func(n *rules.Value) bool {
		if n.Op == nil {
			return ok
		}
		name := n.Op.Name
		switch {
		case a.exts[name] != (ext{}), a.moves[name]:
		case n.Op.IsGeneric() && name == "Select0" && semOps[a.name]["Select0"] != 0:
		case !n.Op.IsGeneric() && semOps[a.name][name] != 0:
		default:
			ok = false
		}
		if n.Ellipsis || n.Rest {
			ok = false
		}
		return ok
	})
	return ok
}

var sampleLeaves = []uint64{
	0x80, 0xff, 0x7f, 0x8000, 0xffff, 0x7fff, 0x80000000, 0xffffffff, 0x7fffffff,
	0, 1, 0x8000000000000000, 0xffffffffffffffff, 0x0123456789abcdef, 0xfedcba9876543210,
	0xffffffffffffff80, 0xffffffffffff8000, 0xffffffff80000000,
}

// checkSemantics compares r's match and result on sample inputs. It
// checks only rules made of ops the evaluator knows that involve an
// extension. It returns a description of a difference, or "".
func checkSemantics(a *archInfo, ot *opTypes, r *rules.Rule) string {
	if r.IsBlock() || r.Result == nil || r.Match.Op == nil || !a.semEvaluable(r.Match) || !a.semEvaluable(r.Result) {
		return ""
	}
	hasExt := false
	for _, v := range []*rules.Value{r.Match, r.Result} {
		v.Walk(func(n *rules.Value) bool {
			if n.Op != nil && a.exts[n.Op.Name] != (ext{}) {
				hasExt = true
			}
			return true
		})
	}
	if !hasExt {
		return ""
	}

	// Leaves get sample values; auxints get their domains.
	var leaves []string
	bound := map[string]*rules.Value{}
	var auxes []auxVar
	ok := true
	r.Match.Walk(func(n *rules.Value) bool {
		if n.Op == nil {
			if !n.IsVar() {
				ok = false // _ or a constant
			}
			leaves = append(leaves, n.Name)
			return true
		}
		if rules.IsVarText(n.Name) {
			bound[n.Name] = n
		}
		if rules.IsVarText(n.AuxInt) {
			if k, ok := kindNames[n.Op.AuxIntType]; ok {
				auxes = append(auxes, auxVar{n.AuxInt, auxDomain(k)})
			}
		}
		return true
	})
	if !ok {
		return ""
	}
	// Only the low bits of the rewritten value's type matter.
	types := ot.ofNode(r.Match)
	if types == 0 {
		types = setOf(tUint64) // unknown: compare whole registers
	}
	size := len(types.all())
	for range leaves {
		size *= len(sampleLeaves)
	}
	for _, x := range auxes {
		size *= len(x.vals)
	}
	if size > 1<<20 {
		return ""
	}

	nl, na := len(leaves), len(auxes)
	idx := make([]int, nl+na+1)
	lim := make([]int, nl+na+1)
	for i := range nl {
		lim[i] = len(sampleLeaves)
	}
	for i, x := range auxes {
		lim[nl+i] = len(x.vals)
	}
	tlist := types.all()
	lim[nl+na] = len(tlist)
	for {
		w := semWorld{env: env{}, leaves: map[string]uint64{}, bound: bound}
		for i, l := range leaves {
			w.leaves[l] = sampleLeaves[idx[i]]
		}
		for i, x := range auxes {
			w.env[x.name] = x.vals[idx[nl+i]]
		}
		t := tlist[idx[nl+na]]
		w.env["v.Type"] = val{k: kType, t: t}
		if rules.IsVarText(r.Match.Type) {
			w.env[r.Match.Type] = val{k: kType, t: t}
		}
		tw := world{env: w.env, types: map[*rules.Value]ssaType{r.Match: t}}
		if mayHold(r.CondExpr, w.env) && constsFit(r.Match, tw) {
			m, ok1 := a.semEval(r.Match, w)
			res, ok2 := a.semEval(r.Result, w)
			bits := min(int(t.size())*8, a.regBits)
			mask := ^uint64(0)
			if bits < 64 {
				mask = 1<<bits - 1
			}
			if ok1 && ok2 && m&mask != res&mask {
				return fmt.Sprintf("match and result differ%s: %s vs %s",
					semWorldDesc(leaves, auxes, w, t), a.hex(int64(m&mask)), a.hex(int64(res&mask)))
			}
		}
		i := 0
		for ; i < len(idx); i++ {
			idx[i]++
			if idx[i] < lim[i] {
				break
			}
			idx[i] = 0
		}
		if i == len(idx) {
			return ""
		}
	}
}

type auxVar struct {
	name string
	vals []val
}

func semWorldDesc(leaves []string, auxes []auxVar, w semWorld, t ssaType) string {
	s := ""
	add := func(x string) {
		if s == "" {
			s = " when "
		} else {
			s += ", "
		}
		s += x
	}
	for _, a := range auxes {
		if v := w.env[a.name]; v.k.isInt() {
			add(fmt.Sprintf("%s=%#x", a.name, v.i))
		}
	}
	for _, l := range leaves {
		add(fmt.Sprintf("%s=%#x", l, w.leaves[l]))
	}
	add("the type is " + t.String())
	return s
}
