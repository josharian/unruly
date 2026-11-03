package facts

import (
	"go/ast"
	"go/types"
	"math/big"
	"math/rand/v2"
	"os"
	"strconv"
	"testing"

	"github.com/josharian/unruly/internal/testenv"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// TestSound checks the facts' claims about every rule of the Go tree
// against concrete evaluation: for random values of each rule's integer
// variables that satisfy its condition, every integer expression of the
// condition and result auxints must lie in its Range, be nonzero if
// NonZero, and equal its mathematical value if Exact.
func TestSound(t *testing.T) {
	c, err := rules.Load(testenv.GoRoot(t))
	if err != nil {
		t.Fatal(err)
	}
	samples := 300
	if os.Getenv("FACTS_SAMPLES") != "" {
		samples, _ = strconv.Atoi(os.Getenv("FACTS_SAMPLES"))
	}
	if testing.Short() {
		samples = 30
	}
	rng := rand.New(rand.NewPCG(1, 2))
	var checked, fired int
	for _, set := range c.Sets {
		res, err := typecheck.Check(set)
		if err != nil {
			t.Fatal(err)
		}
		for _, r := range set.Rules {
			f := New(res, r)
			tr := res.Rule(r)
			var vars []*types.Var
			for _, v := range tr.Vars {
				if isInt(v.Type()) || isBool(v.Type()) {
					vars = append(vars, v)
				}
			}
			var exprs []ast.Expr
			var roots []ast.Expr
			if tr.Cond != nil {
				roots = append(roots, tr.Cond)
			}
			for _, v := range r.ResultValues() {
				v.Walk(func(v *rules.Value) bool {
					if e := tr.Expr(v, typecheck.AuxInt); e != nil {
						roots = append(roots, e)
					}
					return true
				})
			}
			if rb := r.ResultBlock; rb != nil {
				if e := tr.Expr(rb, typecheck.AuxInt); e != nil {
					roots = append(roots, e)
				}
			}
			for _, root := range roots {
				ast.Inspect(root, func(n ast.Node) bool {
					if _, ok := n.(*ast.FuncLit); ok {
						return false
					}
					if e, ok := n.(ast.Expr); ok && isInt(f.typeOf(e, f.root)) {
						if tv, ok := res.Info.Types[e]; ok && !tv.IsType() && tv.Value == nil {
							exprs = append(exprs, e)
						}
					}
					return true
				})
			}
			if len(exprs) == 0 {
				continue
			}
			type claim struct {
				rng     Interval
				ok      bool
				nonzero bool
				exact   bool
				mod64   bool
			}
			claims := make([]claim, len(exprs))
			for i, e := range exprs {
				rg, ok := f.Range(e)
				claims[i] = claim{rg, ok, f.NonZero(e), f.Exact(e), len(f.OverflowsMod(e, 64)) == 0}
			}
			checked++
			for range samples {
				in := &interp{f: f, vals: make(map[types.Object]any)}
				for _, v := range vars {
					in.vals[v] = sample(rng, v.Type(), f.store.get("g:"+v.Name(), full))
				}
				if tr.Cond != nil {
					b, err := in.eval(tr.Cond, f.root, false)
					if err != nil || b != true {
						continue
					}
				}
				fired++
				for i, e := range exprs {
					got, err := in.eval(e, f.root, false)
					if err != nil {
						continue
					}
					x := got.(*big.Int)
					cl := claims[i]
					where := func() string {
						s := r.Pos.String() + ": " + r.Text + "\n\t" + types.ExprString(e) + " with"
						for _, v := range vars {
							s += " " + v.Name() + "=" + fmtVal(in.vals[v])
						}
						return s
					}
					if cl.ok && !point(x).Within(cl.rng) {
						t.Errorf("%s = %v, outside Range %v", where(), x, cl.rng)
					}
					if cl.nonzero && x.Sign() == 0 {
						t.Errorf("%s = 0, but NonZero", where())
					}
					if !cl.exact && !cl.mod64 {
						continue
					}
					m, err := in.eval(e, f.root, true)
					if err != nil {
						continue
					}
					mx := m.(*big.Int)
					if cl.exact && mx.Cmp(x) != 0 {
						t.Errorf("%s = %v, but Exact and mathematically %v", where(), x, mx)
					}
					if cl.mod64 && wrapBits(new(big.Int).Sub(mx, x), 64, true).Sign() != 0 {
						t.Errorf("%s = %v, but OverflowsMod(64) is empty and mathematically %v", where(), x, mx)
					}
				}
			}
		}
	}
	t.Logf("checked %d rules, %d firings", checked, fired)
}

func fmtVal(v any) string {
	switch v := v.(type) {
	case *big.Int:
		return v.String()
	case bool:
		if v {
			return "true"
		}
		return "false"
	}
	return "?"
}

// sample returns a value of t, favoring edge cases,
// including those of known, the facts' range for it.
func sample(rng *rand.Rand, t types.Type, known Interval) any {
	if isBool(t) {
		return rng.IntN(2) == 0
	}
	tr, _ := TypeRange(t)
	var x *big.Int
	switch rng.IntN(8) {
	case 6, 7: // near known's edges
		var e *big.Int
		if rng.IntN(2) == 0 {
			e = known.Lo
		} else {
			e = known.Hi
		}
		if e == nil {
			e = big.NewInt(0)
		}
		x = add(e, big.NewInt(rng.Int64N(5)-2))
	case 0: // small
		x = big.NewInt(rng.Int64N(140) - 70)
	case 1: // ±2^k + {-1, 0, 1}
		x = new(big.Int).Lsh(one, uint(rng.IntN(65)))
		if rng.IntN(2) == 0 {
			x.Neg(x)
		}
		x.Add(x, big.NewInt(rng.Int64N(3)-1))
	case 2: // type edges
		if rng.IntN(2) == 0 {
			x = add(tr.Lo, big.NewInt(rng.Int64N(3)))
		} else {
			x = sub(tr.Hi, big.NewInt(rng.Int64N(3)))
		}
	case 3: // a power of two
		x = new(big.Int).Lsh(one, uint(rng.IntN(64)))
	default:
		x = new(big.Int).SetUint64(rng.Uint64())
	}
	b, _ := basicInt(t)
	w := bits(b)
	if w == 0 {
		w = 64
	}
	return wrapBits(x, w, !unsigned(b))
}
