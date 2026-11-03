// Package auxoverflow defines an analyzer that reports result auxints
// whose value wraps around or is truncated where the op needs it exact.
package auxoverflow

import (
	"fmt"
	"go/ast"
	"go/types"
	"math"
	"math/big"
	"strings"

	"github.com/josharian/unruly/analysis"
	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/ops"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

var Analyzer = &analysis.Analyzer{
	Name: "auxoverflow",
	Doc: `report result auxints that wrap around or are truncated

Auxints are narrower than the values they stand for: a 64-bit
instruction's immediate or a memory op's offset is an int32 that the
assembler sign-extends to 64 bits. A rule that computes such an auxint
with int32 arithmetic, or narrows a wider value into it, must prove that
nothing is lost. For example,

	(MOVOstore [dstOff] {dstSym} ptr (MOVOload [srcOff] {srcSym} (SB) _) mem) && symIsRO(srcSym) =>
	  (MOVQstore [dstOff+8] {dstSym} ptr ... (MOVQstore [dstOff] ...))

computes dstOff+8 in int32. For dstOff = 2147483640 it wraps to
-2147483648, and the second store lands 4 GiB below where it belongs.
Likewise int32(s) for a Move or Zero size s > 2^31 truncates the size.

The analyzer checks each result auxint against what the op does with it,
using the rule's condition (via internal/facts) to prove that the value
fits:

  - a memory op's offset (SymOff, or the offset of a SymValAndOff) is
    added to an address, so it must be exact modulo the address width
    (64 bits, except on 386, ARM, and MIPS, and on Wasm, whose memory
    accesses use the low 32 bits of the address);
  - an int16 or int32 immediate of a wider operation (ADDQconst, S390X
    CMPconst, the value of MOVQstoreconst) must be exact modulo the
    operation's width; that of a 32-bit operation such as ADDLconst
    may wrap, as 32-bit arithmetic does;
  - the value of a SymValAndOff op that does not store it (a size, as
    in S390X CLEAR and MVC) must be exact;
  - on MIPS64, the int64 auxint of an op that codegen emits as an
    immediate operand must fit in int32, since the assembler silently
    truncates wider constants;
  - on x86, an 8-bit count or selector (SHLQconst, VPSLLWconst) must
    not be narrowed from a wider value: uint8(c) of a shift count of
    256 is 0.

Changes of signedness between same-width types, like int32(uint32(c)),
are not reported here; they are a question of how the instruction
extends its immediate.`,
	Run: run,
}

// A check is an expression of an auxint that must not lose
// information, modulo 2^bits (0 means exactly).
type check struct {
	e    ast.Expr
	bits uint
	why  string // how the op uses the value, for the diagnostic
	fit  types.Type

	// narrowing restricts the check to conversions that narrow their
	// operand, as int8(c) does for an int64 c.
	narrowing bool
}

func run(pass *analysis.Pass) error {
	for _, set := range pass.Sets {
		var res *typecheck.Result
		for _, r := range set.Rules {
			if r.Result == nil {
				continue
			}
			var checks []check
			var err error
			for _, top := range r.ResultValues() {
				top.Walk(func(v *rules.Value) bool {
					if v.Op == nil || v.AuxInt == "" || err != nil {
						return err == nil
					}
					if res == nil {
						if res, err = typecheck.Check(set); err != nil {
							return false
						}
					}
					if e := res.Rule(r).Expr(v, typecheck.AuxInt); e != nil {
						checks = append(checks, checksFor(set.Arch, v.Op, e)...)
					}
					return true
				})
			}
			if err != nil {
				return err
			}
			if len(checks) == 0 {
				continue
			}
			f := assumeDomains(facts.New(res, r), set.Arch, r)
			for _, c := range checks {
				if msg := c.problem(f, res.Info); msg != "" {
					pass.Reportf(r.Pos, "%s", msg)
					break
				}
			}
		}
	}
	return nil
}

// checksFor returns the checks of auxint expression e of op.
func checksFor(a *ops.Arch, op *ops.Op, e ast.Expr) []check {
	if a.Generic {
		return nil
	}
	name := op.Name
	switch op.Aux {
	case "SymOff":
		ab := addrBits(a)
		return []check{{e: e, bits: ab, why: fmt.Sprintf("%s's offset is added to a %d-bit address", name, ab)}}
	case "SymValAndOff":
		call, ok := unparen(e).(*ast.CallExpr)
		if !ok || !isFunc(call.Fun, "MakeValAndOff") || len(call.Args) != 2 {
			return nil // e.g. ValAndOff(x).addOffset32(c), guarded by canAdd32
		}
		var cs []check
		if valIsSize(a, op) {
			cs = append(cs, check{e: call.Args[0], why: fmt.Sprintf("%s's value is a size, which must be exact", name)})
		} else if w := opBits(a, op); w > 32 {
			cs = append(cs, check{e: call.Args[0], bits: w, why: fmt.Sprintf("%s sign-extends its 32-bit value to %d bits", name, w)})
		}
		ab := addrBits(a)
		cs = append(cs, check{e: call.Args[1], bits: ab, why: fmt.Sprintf("%s's offset is added to a %d-bit address", name, ab)})
		return cs
	case "Int16", "Int32":
		auxBits := uint(16)
		if op.Aux == "Int32" {
			auxBits = 32
		}
		if zeroExtImm[a.Name+"."+name] {
			return nil
		}
		if w := opBits(a, op); w > auxBits {
			return []check{{e: e, bits: w, why: fmt.Sprintf("%s sign-extends its %d-bit immediate to %d bits", name, auxBits, w)}}
		}
	case "Int8", "UInt8":
		// On x86, an 8-bit auxint of an instruction that does not
		// operate on bytes is an imm8 count or selector: a shift
		// count, a bit index, a SIMD immediate. Arithmetic on these
		// cannot wrap unless an operand is already outside its op's
		// domain, but narrowing a wider value, such as a 64-bit
		// constant, can.
		if a.Name != "AMD64" && a.Name != "386" || opBits(a, op) == 8 {
			return nil
		}
		return []check{{e: e, narrowing: true, why: fmt.Sprintf("%s's 8-bit auxint is a count or selector, so it must be exact", name)}}
	case "Int64":
		if a.Name == "MIPS64" && mips64Imm[name] {
			return []check{{e: e, fit: types.Typ[types.Int32], why: fmt.Sprintf("%s's auxint is an immediate operand, and the MIPS64 assembler silently truncates immediates to 32 bits", name)}}
		}
	}
	return nil
}

// assumeDomains adds to f what is known about r's matched auxints
// beyond their types:
//
//   - The size of a Move or Zero is a type's size, which is not
//     negative.
//   - The offset of an OffPtr of SP is within a stack frame, which is
//     less than 1 GB (ssagen/pgen.go's maxStackSize; larger frames are
//     a compile error).
//   - A MIPS64 immediate fits in int32, which this analyzer checks
//     wherever one is produced.
func assumeDomains(f *facts.Facts, a *ops.Arch, r *rules.Rule) *facts.Facts {
	for _, top := range r.MatchValues() {
		top.Walk(func(v *rules.Value) bool {
			if v.Op == nil || !rules.IsVarText(v.AuxInt) {
				return true
			}
			switch {
			case v.Op.IsGeneric() && (v.Op.Name == "Move" || v.Op.Name == "Zero"):
				f = f.AssumeVar(v.AuxInt, facts.Interval{Lo: big.NewInt(0)})
			case v.Op.IsGeneric() && v.Op.Name == "OffPtr" && len(v.Args) == 1 && v.Args[0].Op != nil && v.Args[0].Op.Name == "SP":
				f = f.AssumeVar(v.AuxInt, facts.Range(-1<<30, 1<<30))
			case a.Name == "MIPS64" && !v.Op.IsGeneric() && mips64Imm[v.Op.Name]:
				f = f.AssumeVar(v.AuxInt, facts.Range(math.MinInt32, math.MaxInt32))
			}
			return true
		})
	}
	return f
}

// problem returns a description of how c's expression may lose
// information, or "" if f proves that it does not.
func (c check) problem(f *facts.Facts, info *types.Info) string {
	if c.fit != nil {
		if f.Fits(c.e, c.fit) {
			return ""
		}
		iv, _ := f.Range(c.e)
		tr, _ := facts.TypeRange(c.fit)
		return fmt.Sprintf("%s may be %s, which does not fit in %s (it is in %s); %s", types.ExprString(c.e), outside(iv, tr), c.fit, iv, c.why)
	}
	var ovs []facts.Overflow
	if c.bits == 0 {
		ovs = f.Overflows(c.e)
	} else {
		ovs = f.OverflowsMod(c.e, c.bits)
	}
	for _, o := range ovs {
		if reinterpretation(info, o.Expr) {
			continue
		}
		if c.narrowing && !narrowing(info, o.Expr) {
			continue
		}
		if truncatesCall(info, o.Expr) {
			// A helper's result, like t.Alignment()'s, can rarely be
			// bounded as tightly as the helper's callers know it is.
			continue
		}
		return describe(info, o, c.why)
	}
	return ""
}

// describe explains overflow o concretely, with a value it may have
// that its type cannot hold.
func describe(info *types.Info, o facts.Overflow, why string) string {
	tr, _ := facts.TypeRange(o.Type)
	w := outside(o.Range, tr)
	verb := "wraps"
	if _, _, ok := conversion(info, o.Expr); ok {
		verb = "truncates"
	}
	return fmt.Sprintf("%s %s in %s: its value may be %s, which becomes %s (it is in %s); %s",
		types.ExprString(o.Expr), verb, o.Type, w, wrap(w, tr), o.Range, why)
}

// outside returns the value of iv closest to range tr but outside it.
func outside(iv, tr facts.Interval) *big.Int {
	if iv.Hi == nil || iv.Hi.Cmp(tr.Hi) > 0 {
		return new(big.Int).Add(tr.Hi, big.NewInt(1))
	}
	return new(big.Int).Sub(tr.Lo, big.NewInt(1))
}

// wrap returns x reduced into range tr, as Go's conversions do.
func wrap(x *big.Int, tr facts.Interval) *big.Int {
	n := new(big.Int).Sub(tr.Hi, tr.Lo)
	n.Add(n, big.NewInt(1))
	y := new(big.Int).Sub(x, tr.Lo)
	y.Mod(y, n)
	return y.Add(y, tr.Lo)
}

// conversion returns the operand of e and the type it is converted to,
// if e is an integer conversion.
func conversion(info *types.Info, e ast.Expr) (x ast.Expr, to types.Type, ok bool) {
	call, ok := unparen(e).(*ast.CallExpr)
	if !ok || len(call.Args) != 1 {
		return nil, nil, false
	}
	tv, ok := info.Types[call.Fun]
	if !ok || !tv.IsType() {
		return nil, nil, false
	}
	return call.Args[0], tv.Type, true
}

// reinterpretation reports whether e is a conversion between integer
// types of the same width, such as int32(uint32(c)).
func reinterpretation(info *types.Info, e ast.Expr) bool {
	x, to, ok := conversion(info, e)
	return ok && intBits(to) != 0 && intBits(to) == intBits(info.TypeOf(x))
}

// narrowing reports whether e is a conversion to a narrower integer
// type.
func narrowing(info *types.Info, e ast.Expr) bool {
	x, to, ok := conversion(info, e)
	return ok && intBits(to) != 0 && intBits(info.TypeOf(x)) > intBits(to)
}

// truncatesCall reports whether e is a conversion of an operand
// computed by calling a function.
func truncatesCall(info *types.Info, e ast.Expr) bool {
	x, _, ok := conversion(info, e)
	return ok && hasCall(info, x)
}

// hasCall reports whether e contains a call other than a conversion.
func hasCall(info *types.Info, e ast.Expr) bool {
	found := false
	ast.Inspect(e, func(n ast.Node) bool {
		if call, ok := n.(*ast.CallExpr); ok {
			if tv, ok := info.Types[call.Fun]; !ok || !tv.IsType() {
				found = true
			}
		}
		return !found
	})
	return found
}

// intBits returns the width of integer type t, or 0 if it is not a
// fixed-width integer type.
func intBits(t types.Type) uint {
	if t == nil {
		return 0
	}
	b, ok := t.Underlying().(*types.Basic)
	if !ok || b.Info()&types.IsInteger == 0 {
		return 0
	}
	switch b.Kind() {
	case types.Int8, types.Uint8:
		return 8
	case types.Int16, types.Uint16:
		return 16
	case types.Int32, types.Uint32:
		return 32
	case types.Int64, types.Uint64:
		return 64
	}
	return 0 // int, uint, uintptr: host-dependent
}

func isFunc(fun ast.Expr, name string) bool {
	switch fun := unparen(fun).(type) {
	case *ast.Ident:
		return fun.Name == name || fun.Name == lowerFirst(name)
	case *ast.SelectorExpr:
		return fun.Sel.Name == name || fun.Sel.Name == lowerFirst(name)
	}
	return false
}

func lowerFirst(s string) string { return strings.ToLower(s[:1]) + s[1:] }

func unparen(e ast.Expr) ast.Expr {
	for {
		p, ok := e.(*ast.ParenExpr)
		if !ok {
			return e
		}
		e = p.X
	}
}
