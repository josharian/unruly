package simdmaskshape

import (
	"fmt"
	"go/ast"
	"go/types"
	"maps"
	"math/big"
	"math/rand/v2"
	"slices"
	"strconv"
	"strings"

	"github.com/josharian/unruly/internal/facts"
	"github.com/josharian/unruly/rules"
	"github.com/josharian/unruly/typecheck"
)

// checkMaskSem evaluates r's match and result on the same inputs, lane
// by lane, and reports a rule whose result computes something else, if
// its match is a modeled op (see lanes.go). It reports only differences
// it finds an input for, in lanes whose values don't depend on unmodeled
// ops: inputs that satisfy the condition's constraints on the rule's
// integer variables (such as an auxint predicate). It does not model
// conditions on the values themselves, so it skips rules whose
// conditions inspect them.
func (c *checker) checkMaskSem(r *rules.Rule) {
	if r.Result == nil || r.Match.Rest || r.Match.Ellipsis {
		return
	}
	in := c.newInterp(r)
	info := classify(r.Match.Op, len(r.Match.Args))
	if info.kind == opaqueOp {
		return
	}
	matchK := writesMask(r.Match.Op)
	bits := info.bits
	if matchK {
		_, bits = in.kShape(r.Match)
	}
	if bits == 0 || bits > 512 || r.Result.Op != nil && writesMask(r.Result.Op) != matchK || inspectsValues(r) {
		return
	}
	sel := in.selectOf(r.Match)
	assigns := c.assignments(r, in)
	trials := min(max(512/max(len(assigns), 1), 8), 64)
	for ai, a := range assigns {
		for t := range trials {
			in.vals = a
			in.newTrial(rand.New(rand.NewPCG(uint64(ai), uint64(t))), t)
			want := in.eval(r.Match, matchK)
			if sel != nil && len(sel.maskVars) > 0 && !reachesAny(r.Result, sel.maskVars, in.bound) && in.dependsOn(r, matchK, sel.maskVars, want, bits) {
				if k, _ := wrapper(r.Match.Op); k == zeroWrapper {
					return // maskedresultdrop reports it
				}
				c.pass.Reportf(r.Pos, "mask dropped: %s selects %s where %s is set and %s elsewhere, but the result %s ignores the mask",
					r.Match.Text, sel.tName, sel.maskDesc, sel.fName, r.Result.Text)
				return
			}
			got := in.eval(r.Result, matchK)
			if !equal(want, got, bits, matchK) {
				c.pass.Reportf(r.Pos, "%s", in.explain(r, sel, want, got, bits, matchK))
				return
			}
		}
	}
}

// equal reports whether a and b agree in their low bits bits (bits
// lanes of a mask register) where both are known.
func equal(a, b val, bits int, isK bool) bool {
	if isK {
		m := ones(bits) &^ (a.ku | b.ku)
		return a.k&m == b.k&m
	}
	for i := range bits / 8 {
		if (a.vu|b.vu)>>i&1 == 0 && a.v[i] != b.v[i] {
			return false
		}
	}
	return true
}

// inspectsValues reports whether r's condition may depend on the
// values matched: if it uses a value variable (including the matched
// value v) other than in x.Uses or clobber(x), or uses v or its block b
// other than through the metadata in allowedPaths or v.Type.
func inspectsValues(r *rules.Rule) bool {
	if r.CondExpr == nil {
		return false
	}
	vals := map[string]bool{"v": true, "b": true}
	for name, occs := range r.MatchVars() {
		if occs[0].Kind == rules.OccValue {
			vals[name] = true
		}
	}
	found := false
	ast.Inspect(r.CondExpr, func(n ast.Node) bool {
		switch x := n.(type) {
		case *ast.SelectorExpr:
			p, root := selPath(x)
			if !vals[root] {
				break
			}
			if allowedPaths[p] || strings.HasPrefix(p, "v.Type.") || p == root+".Uses" {
				return false
			}
			found = true
		case *ast.CallExpr:
			if id, ok := x.Fun.(*ast.Ident); ok && strings.HasPrefix(id.Name, "clobber") {
				return false
			}
		case *ast.Ident:
			found = found || vals[x.Name]
		}
		return !found
	})
	return found
}

// allowedPaths are the selectors of v and b in tip's rule conditions
// that read the block's or function's metadata rather than values.
var allowedPaths = map[string]bool{
	"v.Block.CPUfeatures.HasFeature": true,
	"v.Block.Func.Pass.Name":         true,
	"v.Block.Func.OwnAux.Fn.ABI":     true,
	"v.Pos":                          true,
	"v.Type":                         true,
}

// selPath returns the text of selector x, such as v.Block.Func, and its
// root identifier, or "" if it isn't a chain of selectors of one.
func selPath(x *ast.SelectorExpr) (path, root string) {
	switch y := x.X.(type) {
	case *ast.Ident:
		return y.Name + "." + x.Sel.Name, y.Name
	case *ast.SelectorExpr:
		if p, root := selPath(y); root != "" {
			return p + "." + x.Sel.Name, root
		}
	}
	return "", ""
}

// reachesAny reports whether result v may use any of names, directly or
// through a named match value. A Go expression, such as c.Args[0], may
// use anything.
func reachesAny(v *rules.Value, names []string, bound map[string]*rules.Value) bool {
	found := false
	v.Walk(func(w *rules.Value) bool {
		switch {
		case found:
		case w.IsVar() && slices.Contains(names, w.Name):
			found = true
		case w.IsVar() && bound[w.Name] != nil:
			found = reachesAny(bound[w.Name], names, nil)
		case w.IsLeaf() && !w.IsVar() && w.Name != "_":
			found = len(names) > 0
		}
		return !found
	})
	return found
}

// maskOnly returns the variables that match uses only in its subtree
// mask.
func maskOnly(match, mask *rules.Value) []string {
	count := func(v *rules.Value) map[string]int {
		n := map[string]int{}
		v.Walk(func(w *rules.Value) bool {
			if w.IsVar() && len(w.Args) == 0 {
				n[w.Name]++
			}
			return true
		})
		return n
	}
	all := count(match)
	var names []string
	for name, n := range count(mask) {
		if all[name] == n {
			names = append(names, name)
		}
	}
	slices.Sort(names)
	return names
}

// dependsOn reports whether the match's value want changes when the
// value of one of the variables names is complemented.
func (in *interp) dependsOn(r *rules.Rule, matchK bool, names []string, want val, bits int) bool {
	vecs, ks := in.vecs, in.ks
	defer func() { in.vecs, in.ks = vecs, ks }()
	in.vecs, in.ks = maps.Clone(vecs), maps.Clone(ks)
	for _, name := range names {
		v, isVec := vecs[name]
		k, isK := ks[name]
		if isVec {
			u := *v
			for i := range u {
				u[i] = ^u[i]
			}
			in.vecs[name] = &u
		}
		if isK {
			in.ks[name] = ^k
		}
		other := in.eval(r.Match, matchK)
		if !equal(want, other, bits, matchK) {
			return true
		}
		if isVec {
			in.vecs[name] = v
		}
		if isK {
			in.ks[name] = k
		}
	}
	return false
}

// newInterp returns an interpreter for r.
func (c *checker) newInterp(r *rules.Rule) *interp {
	in := &interp{r: r, bound: map[string]*rules.Value{}, wild: map[*rules.Value]string{}}
	if c.tc != nil {
		if in.tr = c.tc.Rule(r); in.tr != nil {
			in.f = facts.New(c.tc, r)
		}
	}
	r.Match.Walk(func(v *rules.Value) bool {
		switch {
		case !v.IsLeaf() && v.Name != "":
			in.bound[v.Name] = v
		case v.IsLeaf() && v.Name == "_":
			in.wild[v] = fmt.Sprintf("_%d", len(in.wild))
		}
		return true
	})
	return in
}

// assignments returns the values to try for r's integer and boolean
// variables, for which the condition can hold: for each variable, all
// values in its range (as the condition constrains it) if that is
// small, else small values and edge cases; and all combinations of
// those, or, if there are too many, a sample that includes each
// variable's every value.
func (c *checker) assignments(r *rules.Rule, in *interp) []map[types.Object]any {
	if in.tr == nil {
		return []map[types.Object]any{nil}
	}
	var objs []types.Object
	var cands [][]any
	vars := r.MatchVars()
	for _, name := range slices.Sorted(maps.Keys(vars)) {
		obj := in.tr.Vars[name]
		if obj == nil {
			continue
		}
		b, ok := obj.Type().Underlying().(*types.Basic)
		if !ok {
			continue
		}
		var cs []any
		switch {
		case b.Info()&types.IsBoolean != 0:
			cs = []any{false, true}
		case b.Info()&types.IsInteger != 0:
			cs = intCands(in.f, obj.Type(), in.varExpr(vars[name]))
		default:
			continue
		}
		objs = append(objs, obj)
		cands = append(cands, cs)
	}
	const budget = 4096
	total, most := 1, 0
	for _, cs := range cands {
		total = min(total*len(cs), budget+1)
		most = max(most, len(cs))
	}
	var out []map[types.Object]any
	rng := rand.New(rand.NewPCG(uint64(len(objs)), 0))
	for n := range min(total, budget) {
		vals := map[types.Object]any{}
		rest := n
		for i, o := range objs {
			var j int
			switch {
			case total <= budget: // all combinations
				j = rest % len(cands[i])
				rest /= len(cands[i])
			case n < most: // each value
				j = n % len(cands[i])
			default:
				j = rng.IntN(len(cands[i]))
			}
			vals[o] = cands[i][j]
		}
		if in.f.Holds(vals) {
			out = append(out, vals)
		}
	}
	return out
}

// varExpr returns a typed expression for the variable with the given
// occurrences, or nil.
func (in *interp) varExpr(occs []rules.Occurrence) ast.Expr {
	fields := map[rules.OccurrenceKind]typecheck.Field{
		rules.OccValue: typecheck.Name, rules.OccType: typecheck.Type,
		rules.OccAuxInt: typecheck.AuxInt, rules.OccAux: typecheck.Aux,
	}
	for _, o := range occs {
		if o.Value != nil {
			if e := in.tr.Expr(o.Value, fields[o.Kind]); e != nil {
				return e
			}
		}
	}
	return nil
}

// intCands returns the values to try for an integer variable of type
// t, given by expression e.
func intCands(f *facts.Facts, t types.Type, e ast.Expr) []any {
	iv, _ := facts.TypeRange(t)
	if r, ok := f.Range(e); e != nil && ok {
		iv = r
	}
	in := func(x *big.Int) bool {
		return (iv.Lo == nil || iv.Lo.Cmp(x) <= 0) && (iv.Hi == nil || x.Cmp(iv.Hi) <= 0)
	}
	var out []any
	if iv.Bounded() {
		if n := new(big.Int).Sub(iv.Hi, iv.Lo); n.Cmp(big.NewInt(64)) < 0 {
			for i := range n.Int64() + 1 {
				out = append(out, new(big.Int).Add(iv.Lo, big.NewInt(i)))
			}
			return out
		}
	}
	// Small values cover the predicates of compares.
	for x := range int64(64) {
		if b := big.NewInt(x); in(b) {
			out = append(out, b)
		}
	}
	for _, x := range []int64{127, 128, 255, -1, -128} {
		if b := big.NewInt(x); in(b) {
			out = append(out, b)
		}
	}
	for _, b := range []*big.Int{iv.Lo, iv.Hi} {
		if b != nil && !slices.ContainsFunc(out, func(x any) bool { return x.(*big.Int).Cmp(b) == 0 }) {
			out = append(out, b)
		}
	}
	return out
}

// A selInfo describes a select: where mask is set it gives t, elsewhere
// f (0 if f is nil), in w-bit lanes.
type selInfo struct {
	t, f, mask   *rules.Value
	tName, fName string
	maskDesc     string
	maskVars     []string // variables the match uses only in the mask
	w            int
	k            bool // mask is a mask register
}

// selectOf describes v as a select, or returns nil.
func (in *interp) selectOf(v *rules.Value) *selInfo {
	if v.IsLeaf() {
		return nil
	}
	info := classify(v.Op, len(v.Args))
	s := &selInfo{w: info.w}
	switch info.kind {
	case maskMovOp:
		s.t, s.mask, s.k = v.Args[0], v.Args[1], true
	case blendKOp:
		s.t, s.f, s.mask, s.k = v.Args[1], v.Args[0], v.Args[2], true
	case blendVOp:
		s.t, s.f, s.mask = v.Args[1], v.Args[0], v.Args[2]
	case bitOp:
		if !andRE.MatchString(v.Op.Asm) {
			return nil
		}
		a, b := in.vecLane(v.Args[0]), in.vecLane(v.Args[1])
		switch {
		case a == 0 && b != 0:
			s.t, s.mask, s.w = v.Args[0], v.Args[1], b
		case a != 0 && b == 0:
			s.t, s.mask, s.w = v.Args[1], v.Args[0], a
		default:
			return nil
		}
	default:
		return nil
	}
	s.tName, s.fName, s.maskDesc = s.t.Text, "0", in.maskDesc(s.mask)
	if s.k && s.mask.IsLeaf() {
		s.maskDesc = fmt.Sprintf("%s read as one bit per %d-bit lane", s.mask.Text, s.w)
	}
	if s.f != nil {
		s.fName = s.f.Text
	}
	s.maskVars = maskOnly(in.r.Match, s.mask)
	return s
}

// cond reports whether s's mask is set in lane i, and whether that is
// known.
func (in *interp) cond(s *selInfo, i int) (set, known bool) {
	m := in.eval(s.mask, s.k)
	if s.k {
		return m.k>>i&1 != 0, m.ku>>i&1 == 0
	}
	return top(m.v.get(s.w, i), s.w), m.vu>>((i+1)*s.w/8-1)&1 == 0
}

// arms returns the values s selects between.
func (in *interp) arms(s *selInfo) (t, f val) {
	t = in.eval(s.t, false)
	if s.f != nil {
		f = in.eval(s.f, false)
	}
	return t, f
}

// explain describes how got, the result's value, differs from want, the
// match's.
func (in *interp) explain(r *rules.Rule, sel *selInfo, want, got val, bits int, isK bool) string {
	match, res := r.Match.Text, r.Result.Text
	if sel != nil && !r.Result.IsLeaf() {
		if rs := in.selectOf(r.Result); rs != nil {
			for b := range bits / 8 {
				i, j := b*8/sel.w, b*8/rs.w
				mc, ok1 := in.cond(sel, i)
				rc, ok2 := in.cond(rs, j)
				if ok1 && ok2 && mc != rc {
					if p := in.probs(r.Result); len(p) > 0 {
						return strings.Join(p, "; ")
					}
					return in.maskDiff(sel, rs, i, b, match, res)
				}
			}
		}
	}
	if sel != nil {
		t, f := in.arms(sel)
		swapped := true
		for i := range bits / sel.w {
			other := t
			if set, _ := in.cond(sel, i); set {
				other = f
			}
			if got.known(sel.w, i) && other.known(sel.w, i) && want.known(sel.w, i) {
				swapped = swapped && got.v.get(sel.w, i) == other.v.get(sel.w, i)
			}
		}
		if swapped {
			return fmt.Sprintf("operand order: %s selects %s where %s is set and %s elsewhere, but the result %s selects %s there and %s elsewhere",
				match, sel.tName, sel.maskDesc, sel.fName, res, sel.fName, sel.tName)
		}
	}
	if p := in.probs(r.Result); len(p) > 0 {
		return strings.Join(p, "; ")
	}
	if sel == nil {
		return in.laneDiff(r, want, got, bits, isK)
	}
	for i := range bits / sel.w {
		a, b := want.v.get(sel.w, i), got.v.get(sel.w, i)
		set, ok := in.cond(sel, i)
		if a == b || !ok || !want.known(sel.w, i) || !got.known(sel.w, i) {
			continue
		}
		state, gives := "clear", sel.fName
		if set {
			state, gives = "set", sel.tName
		}
		return fmt.Sprintf("selected value: where %s is %s, %s gives %s, but the result %s gives %s",
			sel.maskDesc, state, match, gives, res, in.name(b, sel.w, i))
	}
	return in.laneDiff(r, want, got, bits, isK)
}

// maskDiff describes masks that differ in lane i of match select s and
// in byte b of the result, selected by rs.
func (in *interp) maskDiff(s, rs *selInfo, i, b int, match, res string) string {
	wc, wcmp := in.compareOf(s.mask)
	gc, gcmp := in.compareOf(rs.mask)
	if wc != nil && gc != nil {
		wd, ok1 := in.describeCmp(wc, wcmp)
		ex := in.cmpInputs(wc, wcmp, b*8/wcmp.w, gcmp.cmp.dom)
		gd, ok2 := in.describeCmp(gc, gcmp)
		switch {
		case ok1 && ok2 && wd == gd && s.w != rs.w:
			return fmt.Sprintf("mask granularity: %s selects %d-bit lanes by %s, %s, but the result %s selects %d-bit lanes by it",
				match, s.w, wc.Text, wd, res, rs.w)
		case ok1 && ok2:
			return fmt.Sprintf("compare: %s selects by %s, %s, but the result's %s computes %s%s",
				match, wc.Text, wd, gc.Text, gd, ex)
		}
	}
	return fmt.Sprintf("mask: %s selects by %s, but the result %s selects by %s, which differ in bits %d..%d",
		match, s.maskDesc, res, rs.maskDesc, 8*b, 8*b+7)
}

// compareOf returns the compare that computes mask v, through mask
// conversions, or nil.
func (in *interp) compareOf(v *rules.Value) (*rules.Value, opInfo) {
	for v != nil {
		if v.IsLeaf() {
			v = in.bound[v.Name]
			continue
		}
		info := classify(v.Op, len(v.Args))
		switch info.kind {
		case cmpOp:
			return v, info
		case toKOp, toVecOp:
			v = v.Args[0]
			continue
		}
		break
	}
	return nil, opInfo{}
}

func (in *interp) describeCmp(v *rules.Value, info opInfo) (string, bool) {
	pred := info.cmp.pred
	if pred >= 0 {
		return info.cmp.describe(pred, "", info.w, v.Args[0].Text, v.Args[1].Text), true
	}
	p, ok := in.aux(v)
	if !ok {
		return "", false
	}
	text := ""
	if _, err := strconv.ParseInt(v.AuxInt, 0, 64); err != nil {
		text = v.AuxInt
	}
	return info.cmp.describe(p, text, info.w, v.Args[0].Text, v.Args[1].Text), true
}

// cmpInputs describes compare v's operands in element i, if they are
// variables.
// If dom, another compare's domain, differs from v's, it shows them
// in both.
func (in *interp) cmpInputs(v *rules.Value, info opInfo, i int, dom string) string {
	var parts []string
	for _, a := range v.Args {
		if !a.IsVar() || in.bound[a.Name] != nil {
			return ""
		}
		x := in.vecVar(a.Name).get(info.w, i)
		p := a.Name + " = " + fmtElem(x, info.w, info.cmp.dom)
		if dom != info.cmp.dom && (dom == "float" || info.cmp.dom == "float") {
			p += " (" + fmtElem(x, info.w, dom) + ")"
		}
		parts = append(parts, p)
	}
	return fmt.Sprintf(": they differ where %s", strings.Join(parts, " and "))
}

func fmtElem(x uint64, w int, dom string) string {
	switch dom {
	case "float":
		return strconv.FormatFloat(float(x, w), 'g', 4, 64)
	case "signed":
		if s := sext(x, w); -1<<16 < s && s < 1<<16 {
			return strconv.FormatInt(s, 10)
		}
	}
	if x < 1<<16 {
		return strconv.FormatUint(x, 10)
	}
	return fmt.Sprintf("%#x", x)
}

// name names w-bit value x in lane i: 0, a variable whose lane i it
// is, or its value.
func (in *interp) name(x uint64, w, i int) string {
	if x == 0 {
		return "0"
	}
	for _, n := range slices.Sorted(maps.Keys(in.vecs)) {
		if !strings.HasPrefix(n, "_") && in.vecs[n].get(w, i) == x {
			return n
		}
	}
	return fmt.Sprintf("%#x", x)
}

// laneDiff describes the first lane in which got differs from want.
func (in *interp) laneDiff(r *rules.Rule, want, got val, bits int, isK bool) string {
	setOrClear := func(set bool) string {
		if set {
			return "sets"
		}
		return "clears"
	}
	if isK {
		w, _ := in.kShape(r.Match)
		for i := range bits {
			if a, b := want.k>>i&1 != 0, got.k>>i&1 != 0; a != b && (want.ku|got.ku)>>i&1 == 0 {
				return fmt.Sprintf("lane-wise: %s %s mask bit %d, but the result %s %s it%s",
					r.Match.Text, setOrClear(a), i, r.Result.Text, setOrClear(b), in.laneInputs(r, w, i))
			}
		}
	}
	w := in.vecLane(r.Match)
	isMask := w != 0
	if w == 0 {
		w = max(classify(r.Match.Op, len(r.Match.Args)).w, 8)
	}
	for i := range bits / w {
		a, b := want.v.get(w, i), got.v.get(w, i)
		switch {
		case a == b || !want.known(w, i) || !got.known(w, i):
		case isMask && (b == 0 || b == ones(w)):
			return fmt.Sprintf("lane-wise: %s %s %d-bit lane %d, but the result %s %s it%s",
				r.Match.Text, setOrClear(a != 0), w, i, r.Result.Text, setOrClear(b != 0), in.laneInputs(r, w, i))
		default:
			return fmt.Sprintf("lane-wise: %s gives %s in %d-bit lane %d, but the result %s gives %s%s",
				r.Match.Text, in.name(a, w, i), w, i, r.Result.Text, in.name(b, w, i), in.laneInputs(r, w, i))
		}
	}
	return "lane-wise: " + r.Match.Text + " differs from " + r.Result.Text
}

// laneInputs describes the inputs to lane i, of w bits, of r's match:
// the operands of its compares, or else its variables.
func (in *interp) laneInputs(r *rules.Rule, w, i int) string {
	var parts []string
	seen := map[string]bool{}
	add := func(name, val string) {
		if !seen[name] {
			seen[name] = true
			parts = append(parts, name+" = "+val)
		}
	}
	r.Match.Walk(func(v *rules.Value) bool {
		info := classify(v.Op, len(v.Args))
		if v.IsLeaf() || info.kind != cmpOp || w == 0 {
			return true
		}
		for _, a := range v.Args {
			if a.IsVar() && in.bound[a.Name] == nil {
				add(a.Name, fmtElem(in.vecVar(a.Name).get(info.w, i*w/info.w), info.w, info.cmp.dom))
			}
		}
		return true
	})
	if len(parts) == 0 {
		for _, n := range slices.Sorted(maps.Keys(in.ks)) {
			if strings.HasPrefix(n, "_") {
				continue
			}
			add(fmt.Sprintf("%s's bit %d", n, i), fmt.Sprint(in.ks[n]>>i&1))
		}
		for _, n := range slices.Sorted(maps.Keys(in.vecs)) {
			if w != 0 && !strings.HasPrefix(n, "_") {
				add(n+fmt.Sprintf("'s lane %d", i), fmt.Sprintf("%#x", in.vecs[n].get(w, i)))
			}
		}
	}
	for _, o := range slices.SortedFunc(maps.Keys(in.vals), func(a, b types.Object) int { return strings.Compare(a.Name(), b.Name()) }) {
		add(o.Name(), fmt.Sprint(in.vals[o]))
	}
	if len(parts) == 0 {
		return ""
	}
	return ", where " + strings.Join(parts, ", ")
}

// vecLane returns the width of the lanes in which vector v is all ones
// or all zeros, or 0 if unknown.
func (in *interp) vecLane(v *rules.Value) int {
	if v.IsLeaf() {
		if b := in.bound[v.Name]; b != nil {
			return in.vecLane(b)
		}
		return 0
	}
	info := classify(v.Op, len(v.Args))
	switch info.kind {
	case cmpOp:
		if !writesMask(v.Op) {
			return info.w
		}
	case toVecOp:
		return info.w
	case bitOp:
		if andRE.MatchString(v.Op.Asm) {
			a, b := in.vecLane(v.Args[0]), in.vecLane(v.Args[1])
			if a != 0 && b != 0 {
				return min(a, b)
			}
		}
	}
	return 0
}

// kShape returns the lane width that each bit of mask register v stands
// for, and the number of its meaningful bits, or 0s if unknown.
func (in *interp) kShape(v *rules.Value) (lane, lanes int) {
	if v.IsLeaf() {
		if b := in.bound[v.Name]; b != nil {
			return in.kShape(b)
		}
		return 0, 0
	}
	info := classify(v.Op, len(v.Args))
	switch info.kind {
	case cmpOp:
		return info.w, info.bits / info.w
	case toKOp:
		return info.w, info.lanes
	}
	return 0, 0
}

// maskDesc describes mask v for diagnostics.
func (in *interp) maskDesc(v *rules.Value) string {
	return v.Text
}

// probs returns problems with how result v's ops read their masks,
// which explain why it differs from the match.
func (in *interp) probs(v *rules.Value) []string {
	var out []string
	add := func(format string, args ...any) {
		p := fmt.Sprintf(format, args...)
		if !slices.Contains(out, p) {
			out = append(out, p)
		}
	}
	v.Walk(func(v *rules.Value) bool {
		if v.IsLeaf() {
			return false
		}
		info := classify(v.Op, len(v.Args))
		read := func(m *rules.Value) {
			if l := in.vecLane(m); l != 0 && info.w > l {
				add("mask granularity: %s reads the top bit of each %d-bit lane, but its mask %s has %d-bit lanes, so it ignores %d of every %d of them",
					v.Op.Name, info.w, in.maskDesc(m), l, info.w/l-1, info.w/l)
			}
		}
		consume := func(k *rules.Value, lanes int) {
			kl, kn := in.kShape(k)
			switch {
			case kl != 0 && kl != info.w:
				unit := "lane"
				if c, _ := in.compareOf(k); c != nil {
					unit = "element"
				}
				add("mask lane width: %s takes one mask bit per %d-bit lane, but its mask %s has one bit per %d-bit %s, so %s",
					v.Op.Name, info.w, k.Text, kl, unit, misread(info.w, kl, unit))
			case kn != 0 && lanes != 0 && kn != lanes:
				add("mask lanes: %s takes %d mask bits, but its mask %s has %d", v.Op.Name, lanes, k.Text, kn)
			}
		}
		switch info.kind {
		case toKOp:
			read(v.Args[0])
		case blendVOp:
			read(v.Args[2])
		case maskMovOp:
			consume(v.Args[1], info.bits/info.w)
		case blendKOp:
			consume(v.Args[2], info.bits/info.w)
		case toVecOp:
			consume(v.Args[0], info.lanes)
		}
		return true
	})
	return out
}

// misread explains what goes wrong when lane i of w bits is selected by
// the bit for element i of e bits.
func misread(w, e int, unit string) string {
	if w > e {
		return fmt.Sprintf("lane i is selected by %s i instead of %ss %d*i..%d*i+%d", unit, unit, w/e, w/e, w/e-1)
	}
	return fmt.Sprintf("lane i is selected by %s i instead of %s i/%d", unit, unit, e/w)
}
