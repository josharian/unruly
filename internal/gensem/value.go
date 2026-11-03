package gensem

import (
	"fmt"
	"math"
	"math/bits"
	"strings"
	"sync"

	"github.com/josharian/unruly/ops"
)

// Value models an SSA value.
//
// A Value with a nil Op is a leaf: a value computed by something the
// model leaves opaque (a function argument, a load, ...), whose run-time
// value is Leaf.
type Value struct {
	Op     *ops.Op
	Type   *Type
	AuxInt int64
	Aux    any // a *Sym, for ops whose aux is a symbol
	Args   []*Value
	Uses   int32
	Leaf   Val
	Name   string // for leaves: a name for printing, such as the rule variable it stands for
}

// OpName returns v's qualified op name, or "" for a leaf.
func (v *Value) OpName() string {
	if v.Op == nil {
		return ""
	}
	return v.Op.QualifiedName()
}

// Sym is a symbol: a variable whose address Addr or LocalAddr takes.
type Sym struct {
	Obj   int // the variable's object, for KPtr values
	Local bool
}

func (s *Sym) String() string {
	if s.Local {
		return fmt.Sprintf("local%d", s.Obj)
	}
	return fmt.Sprintf("global%d", s.Obj)
}

// Config models the parts of ssa.Config that rules consult.
type Config struct {
	Arch      string // GOARCH, as in ssa.Config.Arch: "amd64", "386", ...
	PtrSize   int64
	RegSize   int64
	BigEndian bool
	// Pass is the name of the compiler pass applying the rules,
	// as in v.Block.Func.Pass.Name.
	Pass string
}

func (c *Config) String() string { return c.Arch }

// Configs are representative targets: a rule must be correct on each.
var Configs = []*Config{
	{Arch: "amd64", PtrSize: 8, RegSize: 8},
	{Arch: "386", PtrSize: 4, RegSize: 4},
	{Arch: "arm64", PtrSize: 8, RegSize: 8},
	{Arch: "s390x", PtrSize: 8, RegSize: 8, BigEndian: true},
	{Arch: "arm", PtrSize: 4, RegSize: 4},
	{Arch: "wasm", PtrSize: 8, RegSize: 8},
}

// ArchConfigs returns the targets of a rules arch, such as "AMD64" or
// "MIPS64", from ssacompile/config.go's NewConfig, or nil if unknown.
// The generic arches (generic, dec, divmod, ...) run on every target;
// for them it returns Configs. The result is the same for each call.
func ArchConfigs(arch string) []*Config {
	archConfigsMu.Lock()
	defer archConfigsMu.Unlock()
	if cs, ok := archConfigs[arch]; ok {
		return cs
	}
	cs := archConfigs1(arch)
	// The passes that apply each generic arch's rules (ssacompile/compile.go).
	var passes []string
	switch arch {
	case "generic":
		passes = []string{"opt", "late opt"}
	case "dec64", "dec":
		passes = []string{"decompose builtin"}
	case "divmod":
		passes = []string{"divmod"}
	case "divisible":
		passes = []string{"divisible"}
	default:
		passes = []string{"lower"}
	}
	var res []*Config
	for _, p := range passes {
		for _, c := range cs {
			c := *c
			c.Pass = p
			res = append(res, &c)
		}
	}
	archConfigs[arch] = res
	return res
}

var (
	archConfigsMu sync.Mutex
	archConfigs   = map[string][]*Config{}
)

func archConfigs1(arch string) []*Config {
	switch arch {
	case "386":
		return []*Config{{Arch: "386", PtrSize: 4, RegSize: 4}}
	case "AMD64":
		return []*Config{{Arch: "amd64", PtrSize: 8, RegSize: 8}}
	case "ARM":
		return []*Config{{Arch: "arm", PtrSize: 4, RegSize: 4}}
	case "ARM64":
		return []*Config{{Arch: "arm64", PtrSize: 8, RegSize: 8}}
	case "LOONG64":
		return []*Config{{Arch: "loong64", PtrSize: 8, RegSize: 8}}
	case "MIPS":
		return []*Config{{Arch: "mips", PtrSize: 4, RegSize: 4, BigEndian: true}, {Arch: "mipsle", PtrSize: 4, RegSize: 4}}
	case "MIPS64":
		return []*Config{{Arch: "mips64", PtrSize: 8, RegSize: 8, BigEndian: true}, {Arch: "mips64le", PtrSize: 8, RegSize: 8}}
	case "PPC64":
		return []*Config{{Arch: "ppc64", PtrSize: 8, RegSize: 8, BigEndian: true}, {Arch: "ppc64le", PtrSize: 8, RegSize: 8}}
	case "RISCV64":
		return []*Config{{Arch: "riscv64", PtrSize: 8, RegSize: 8}}
	case "S390X":
		return []*Config{{Arch: "s390x", PtrSize: 8, RegSize: 8, BigEndian: true}}
	case "Wasm":
		return []*Config{{Arch: "wasm", PtrSize: 8, RegSize: 8}}
	case "dec64":
		// dec64 decomposes 64-bit integers on 32-bit targets.
		var cs []*Config
		for _, c := range Configs {
			if c.RegSize == 4 {
				cs = append(cs, c)
			}
		}
		return cs
	}
	return Configs
}

// Unsupported reports something the model does not cover.
type Unsupported struct{ What string }

func (e *Unsupported) Error() string { return "unsupported: " + e.What }

func unsupported(format string, args ...any) error {
	return &Unsupported{fmt.Sprintf(format, args...)}
}

// Undefined reports an op applied outside its defined domain, such as a
// bounded shift by its width or Avg64u with arg0 < arg1. Such a value
// cannot occur in valid SSA.
type Undefined struct {
	Op  string
	Msg string
}

func (e *Undefined) Error() string { return e.Op + ": " + e.Msg }

// Unspecified reports an op whose result for its args is valid SSA but
// differs between machines, such as converting an out-of-range float to
// an integer.
type Unspecified struct {
	Op  string
	Msg string
}

func (e *Unspecified) Error() string {
	return e.Op + ": " + e.Msg + "; the result is machine-dependent"
}

// IllTyped reports an op applied to args of the wrong kind or width.
type IllTyped struct {
	Op  string
	Msg string
}

func (e *IllTyped) Error() string { return e.Op + ": " + e.Msg }

// Panic reports a Go run-time panic while evaluating a rule's Go code,
// which would crash the compiler.
type Panic struct{ Msg string }

func (e *Panic) Error() string { return "panic: " + e.Msg }

// OpFunc computes the value of v, whose args have values args.
type OpFunc func(in *OpInput) (Val, error)

// OpInput is the input to an OpFunc.
type OpInput struct {
	V       *Value
	Args    []Val
	Cfg     *Config
	Garbage uint64 // seeds the upper bits of narrow args read as wider
}

// Interp evaluates Value trees.
type Interp struct {
	Cfg *Config
	Ops map[string]OpFunc // by qualified op name
	// Garbage seeds the unspecified upper bits of narrow values
	// that ops read as wider.
	Garbage uint64

	memo map[*Value]result
}

type result struct {
	val Val
	err error
}

// NewInterp returns an interpreter for cfg using the given op semantics.
func NewInterp(cfg *Config, opFuncs map[string]OpFunc) *Interp {
	return &Interp{Cfg: cfg, Ops: opFuncs, memo: map[*Value]result{}}
}

// Reset forgets memoized values.
func (in *Interp) Reset() { clear(in.memo) }

// Eval returns the run-time value of v.
func (in *Interp) Eval(v *Value) (Val, error) {
	if v.Op == nil {
		return v.Leaf, nil
	}
	if r, ok := in.memo[v]; ok {
		return r.val, r.err
	}
	val, err := in.eval(v)
	in.memo[v] = result{val, err}
	return val, err
}

func (in *Interp) eval(v *Value) (Val, error) {
	f := in.Ops[v.Op.QualifiedName()]
	if f == nil {
		return Val{}, unsupported("op %s", v.Op.QualifiedName())
	}
	args := make([]Val, len(v.Args))
	for i, a := range v.Args {
		x, err := in.Eval(a)
		if err != nil {
			return Val{}, err
		}
		args[i] = x
	}
	return f(&OpInput{V: v, Args: args, Cfg: in.Cfg, Garbage: in.Garbage})
}

// Format formats v as an s-expression, with the value of each leaf.
func (in *Interp) Format(v *Value) string { return in.FormatAll(v)[0] }

// FormatAll formats each of vs as Format does, showing the value of a
// named leaf only where it first appears.
func (in *Interp) FormatAll(vs ...*Value) []string {
	seen := map[*Value]bool{}
	var res []string
	for _, v := range vs {
		var b strings.Builder
		in.format(&b, v, seen)
		res = append(res, b.String())
	}
	return res
}

func (in *Interp) format(b *strings.Builder, v *Value, seen map[*Value]bool) {
	if v.Op == nil {
		if v.Name != "" {
			b.WriteString(v.Name)
			if !seen[v] {
				fmt.Fprintf(b, "=%s", v.Leaf)
			}
		} else {
			b.WriteString(v.Leaf.String())
		}
		seen[v] = true
		return
	}
	b.WriteString("(" + v.Op.QualifiedName())
	if v.Op.HasAuxInt && !(v.Op.AuxIntType == "bool" && v.AuxInt == 0) {
		fmt.Fprintf(b, " [%s]", formatAuxInt(v))
	}
	if v.Aux != nil {
		fmt.Fprintf(b, " {%v}", v.Aux)
	}
	for _, a := range v.Args {
		b.WriteString(" ")
		in.format(b, a, seen)
	}
	b.WriteString(")")
}

func formatAuxInt(v *Value) string {
	switch v.Op.AuxIntType {
	case "float32", "float64":
		return FloatVal(64, Val{Kind: KFloat, Width: 64, Bits: uint64(v.AuxInt)}.Float()).String()
	case "bool":
		return fmt.Sprint(v.AuxInt != 0)
	}
	return fmt.Sprint(v.AuxInt)
}

// A Slot is a mutable scalar in a value tree: a leaf's value or an
// AuxInt, used to simplify counterexamples.
type Slot struct {
	v *Value
}

// Slots returns the slots of the tree v, each once.
func Slots(v *Value) []Slot {
	var res []Slot
	seen := map[*Value]bool{}
	var walk func(v *Value)
	walk = func(v *Value) {
		if seen[v] {
			return
		}
		seen[v] = true
		switch {
		case v.Op == nil:
			if v.Leaf.Kind == KInt || v.Leaf.Kind == KFloat {
				res = append(res, Slot{v})
			}
		case v.Op.HasAuxInt:
			switch v.Op.AuxIntType {
			case "int8", "int16", "int32", "int64", "float32", "float64", "bool":
				res = append(res, Slot{v})
			}
		}
		for _, a := range v.Args {
			walk(a)
		}
	}
	walk(v)
	return res
}

// Get returns the slot's current contents.
func (s Slot) Get() uint64 {
	if s.v.Op == nil {
		return s.v.Leaf.Bits
	}
	return uint64(s.v.AuxInt)
}

// Set sets the slot's contents.
func (s Slot) Set(x uint64) {
	if s.v.Op == nil {
		s.v.Leaf.Bits = x
		return
	}
	s.v.AuxInt = int64(x)
}

// Simpler returns simpler contents to try, simplest first.
func (s Slot) Simpler() []uint64 {
	cur := s.Get()
	var float bool
	var w int
	switch {
	case s.v.Op == nil:
		float, w = s.v.Leaf.Kind == KFloat, s.v.Leaf.Width
	case s.v.Op.AuxIntType == "bool":
		if cur != 0 {
			return []uint64{0}
		}
		return nil
	case s.v.Op.AuxIntType == "float32" || s.v.Op.AuxIntType == "float64":
		float = true
	default:
		w = map[string]int{"int8": 8, "int16": 16, "int32": 32, "int64": 64}[s.v.Op.AuxIntType]
	}
	var res []uint64
	if float {
		get := func(x uint64) float64 {
			if s.v.Op == nil {
				return Val{Kind: KFloat, Width: w, Bits: x}.Float()
			}
			return math.Float64frombits(x)
		}
		put := func(f float64) uint64 {
			if s.v.Op == nil {
				return FloatVal(w, f).Bits
			}
			return math.Float64bits(f)
		}
		f := get(cur)
		for _, c := range []float64{0, 1, -1, 2, math.Trunc(f), math.Trunc(f / 2), math.Trunc(f / 1024)} {
			if c != f && !math.IsNaN(c) && math.Abs(c) < math.Abs(f) || math.IsNaN(f) && !math.IsNaN(c) {
				res = append(res, put(c))
			}
		}
		return res
	}
	x := sext(cur, w)
	cost := func(y int64) int {
		if y < 0 {
			y = -y
		}
		return bits.Len64(uint64(y))
	}
	for _, c := range []int64{0, 1, -1, 2, x / 2, x / 16, x >> 1 & ^int64(0) >> 1, -x, x &^ (x & -x) /* clear lowest bit */} {
		c = sext(uint64(c), w)
		if cost(c) < cost(x) || cost(c) == cost(x) && c >= 0 && x < 0 {
			enc := uint64(c)
			if s.v.Op == nil {
				enc &= mask(w)
			}
			res = append(res, enc)
		}
	}
	return res
}
