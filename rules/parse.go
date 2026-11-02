package rules

import (
	"errors"
	"fmt"
	"go/parser"
	"go/token"
	"strings"

	"github.com/josharian/unruly/ops"
)

// ParseFile parses the rules file at path, whose content is src, resolving
// ops and blocks for arch. Rules with errors are omitted from the result.
//
// ParseFile rejects everything rulegen rejects when reading rules (unknown
// ops, wrong argument counts, aux on ops without aux, untyped result
// sub-expressions, malformed block rules, misused ... and ___, ...), and a few
// things rulegen would accept but turn into broken Go code.
// It does not check properties of a whole rule set, such as an unconditional
// rule followed by another rule for the same op; see RuleSet.
func ParseFile(path string, src []byte, arch *ops.Arch) (*File, []error) {
	raws, errs := scanRules(path, src)
	f := &File{Path: path}
	p := &ruleParser{arch: arch}
	for _, raw := range raws {
		pos := Pos{path, raw.start}
		rules, err := p.rule(raw, pos)
		if err != nil {
			errs = append(errs, &Error{pos, err.Error()})
			continue
		}
		for _, r := range rules {
			r.File = f
		}
		f.Rules = append(f.Rules, rules...)
	}
	return f, errs
}

type ruleParser struct {
	arch *ops.Arch
}

// predeclared names are never declared by rulegen; in a match,
// they are always compared against.
var predeclared = map[string]bool{
	"nil":   true,
	"false": true,
	"true":  true,
}

func (p *ruleParser) rule(raw rawRule, pos Pos) ([]*Rule, error) {
	alts, err := expandOr(raw.text)
	if err != nil {
		return nil, err
	}
	var rules []*Rule
	for i, alt := range alts {
		r := &Rule{
			Pos:     pos,
			EndLine: raw.end,
			Orig:    normalizeSpaces(raw.text),
			Text:    normalizeSpaces(alt),
			Alt:     i,
			NumAlts: len(alts),
		}
		if err := p.parseRule(r, alt); err != nil {
			if len(alts) > 1 {
				err = fmt.Errorf("%v (in expansion %q)", err, r.Text)
			}
			return nil, err
		}
		rules = append(rules, r)
	}
	return rules, nil
}

func (p *ruleParser) parseRule(r *Rule, text string) error {
	parts := strings.Split(text, "=>")
	if len(parts) != 2 {
		return errors.New("rule must contain exactly one =>")
	}
	match := normalizeSpaces(parts[0])
	result := normalizeSpaces(parts[1])
	cond := ""
	if i := strings.Index(match, "&&"); i >= 0 {
		cond = normalizeSpaces(match[i+2:])
		match = normalizeSpaces(match[:i])
	}
	r.MatchText, r.Cond, r.ResultText = match, cond, result
	if cond != "" {
		x, err := parser.ParseExpr(cond)
		if err != nil {
			return fmt.Errorf("failed to parse cond %q: %v", cond, err)
		}
		r.CondExpr = x
	}
	if !strings.HasPrefix(match, "(") {
		return fmt.Errorf("match %q is not a parenthesized s-expression", match)
	}
	if result == "" {
		return errors.New("empty result")
	}

	// rulegen decides between value and block rules by the rule's first token.
	first, _, _ := strings.Cut(strings.TrimSpace(text), " ")
	if p.arch.LookupBlock(first[1:]) != nil {
		return p.blockRule(r)
	}

	m, err := p.matchValue(match)
	if err != nil {
		return err
	}
	r.Match = m

	if result[0] == '@' {
		s := strings.SplitN(result[1:], " ", 2)
		if len(s) != 2 {
			return fmt.Errorf("malformed @block result %q", result)
		}
		r.Placement, result = s[0], s[1]
	}
	if result[0] == '{' {
		if result[len(result)-1] != '}' {
			return fmt.Errorf("malformed {code} result %q", result)
		}
		r.ResultCode = result[1 : len(result)-1]
	} else {
		res, err := p.resultArg(result, true, r.Placement != "")
		if err != nil {
			return err
		}
		r.Result = res
	}
	if err := checkEllipsis(r); err != nil {
		return err
	}
	return p.checkMatchNames(r)
}

// matchArg parses an argument of a match s-expression.
func (p *ruleParser) matchArg(arg string) (*Value, error) {
	if !strings.Contains(arg, "(") {
		if !token.IsIdentifier(arg) {
			return nil, fmt.Errorf("invalid match variable %q", arg)
		}
		return &Value{Text: arg, Name: arg}, nil
	}
	name, expr, err := splitNameExpr(arg)
	if err != nil {
		return nil, err
	}
	if name == "b" {
		return nil, errors.New("don't name args 'b', it is ambiguous with blocks")
	}
	if name != "" && !token.IsIdentifier(name) {
		return nil, fmt.Errorf("invalid name %q", name)
	}
	v, err := p.matchValue(expr)
	if err != nil {
		return nil, err
	}
	v.Name = name
	return v, nil
}

func (p *ruleParser) matchValue(s string) (*Value, error) {
	v, args, err := p.value(s)
	if err != nil {
		return nil, err
	}
	for i, a := range args {
		if a == "___" {
			if i != len(args)-1 {
				return nil, fmt.Errorf("___ must be the last argument in %s", s)
			}
			v.Rest = true
			continue
		}
		arg, err := p.matchArg(a)
		if err != nil {
			return nil, err
		}
		v.Args = append(v.Args, arg)
	}
	if v.Rest && v.Op.ArgLength != -1 {
		return nil, fmt.Errorf("___ used with op %s, which is not variadic", v.Op)
	}
	return v, nil
}

// resultArg parses an argument of a result s-expression,
// or the top-level result if top is set.
func (p *ruleParser) resultArg(arg string, top, placed bool) (*Value, error) {
	name, expr, err := splitNameExpr(arg)
	if err != nil {
		return nil, err
	}
	if expr == "" {
		return nil, fmt.Errorf("empty result expression %q", arg)
	}
	if expr[0] != '(' {
		if name != "" {
			return nil, fmt.Errorf("result %q names a non-s-expression", arg)
		}
		if expr == "___" || expr == "..." {
			return nil, fmt.Errorf("%s not allowed here in result", expr)
		}
		return &Value{Text: expr, Name: expr}, nil
	}
	if p.arch.Tables().ReservedNames[name] {
		return nil, fmt.Errorf("rule uses the reserved name %s", name)
	}
	v, args, err := p.value(expr)
	if err != nil {
		return nil, err
	}
	v.Name = name
	if v.Ellipsis && !top {
		return nil, fmt.Errorf("... not allowed in result sub-expression %s", expr)
	}
	for _, a := range args {
		if a == "___" {
			return nil, fmt.Errorf("___ not allowed in result %s", expr)
		}
		c, err := p.resultArg(a, false, placed)
		if err != nil {
			return nil, err
		}
		v.Args = append(v.Args, c)
	}
	if (!top || placed) && v.Type == "" && v.Op.Typ == "" {
		return nil, fmt.Errorf("sub-expression %s (op=Op%s) must have a type", expr, v.Op.QualifiedName())
	}
	return v, nil
}

// value parses the parts of s-expression s common to matches and results,
// returning the remaining unparsed args, excluding "...".
func (p *ruleParser) value(s string) (*Value, []string, error) {
	op, typ, auxint, aux, args, err := extract(s)
	if err != nil {
		return nil, nil, err
	}
	v := &Value{Text: s, OpName: op, Type: typ, AuxInt: auxint, Aux: aux}
	nargs := len(args)
	if len(args) > 0 && args[len(args)-1] == "..." {
		if len(args) != 1 {
			return nil, nil, fmt.Errorf("... must be the only argument in %s", s)
		}
		v.Ellipsis = true
		args = nil
	}
	v.Op, err = p.arch.ResolveOp(op, nargs, v.Ellipsis)
	if err != nil {
		return nil, nil, err
	}
	if auxint != "" && !v.Op.HasAuxInt {
		return nil, nil, fmt.Errorf("op %s %s can't have auxint", op, v.Op.Aux)
	}
	if aux != "" && !v.Op.HasAux {
		return nil, nil, fmt.Errorf("op %s %s can't have aux", op, v.Op.Aux)
	}
	for _, a := range args {
		if a == "..." {
			return nil, nil, fmt.Errorf("... must be the only argument in %s", s)
		}
	}
	return v, args, nil
}

func (p *ruleParser) blockRule(r *Rule) error {
	mb, args, err := p.block(r.MatchText)
	if err != nil {
		return err
	}
	for _, a := range args[:mb.Info.Controls] {
		c, err := p.matchArg(a)
		if err != nil {
			return err
		}
		mb.Controls = append(mb.Controls, c)
	}
	mb.Succs = args[mb.Info.Controls:]

	if !strings.HasPrefix(r.ResultText, "(") {
		return fmt.Errorf("block rule result %q is not a parenthesized s-expression", r.ResultText)
	}
	rb, args, err := p.block(r.ResultText)
	if err != nil {
		return err
	}
	for _, a := range args[:rb.Info.Controls] {
		c, err := p.resultArg(a, false, false)
		if err != nil {
			return err
		}
		rb.Controls = append(rb.Controls, c)
	}
	rb.Succs = args[rb.Info.Controls:]
	r.MatchBlock, r.ResultBlock = mb, rb

	// Successors may only be kept or swapped.
	seen := map[string]bool{}
	for _, s := range mb.Succs {
		if !token.IsIdentifier(s) {
			return fmt.Errorf("invalid successor name %q", s)
		}
		if seen[s] {
			return fmt.Errorf("can't have a repeat successor name %s", s)
		}
		seen[s] = true
	}
	for _, s := range rb.Succs {
		if !seen[s] {
			return fmt.Errorf("unknown successor %s", s)
		}
		delete(seen, s)
	}
	if len(seen) != 0 {
		return fmt.Errorf("unmatched successors %v", seen)
	}
	changed := false
	for i := range mb.Succs {
		changed = changed || mb.Succs[i] != rb.Succs[i]
	}
	if changed && (len(mb.Succs) != 2 || mb.Succs[0] != rb.Succs[1]) {
		return errors.New("can only handle swapped successors")
	}
	return p.checkMatchNames(r)
}

// block parses a block s-expression, returning its unparsed controls and
// successors.
func (p *ruleParser) block(s string) (*Block, []string, error) {
	kind, typ, auxint, aux, args, err := extract(s)
	if err != nil {
		return nil, nil, err
	}
	info := p.arch.LookupBlock(kind)
	if info == nil {
		return nil, nil, fmt.Errorf("could not find block data for %s", kind)
	}
	if len(args) < info.Controls {
		return nil, nil, fmt.Errorf("incorrect number of arguments in %s, got %v wanted at least %v", s, len(args), info.Controls)
	}
	if auxint != "" && !validAuxType(info.AuxIntType) {
		return nil, nil, fmt.Errorf("block %s has no auxint", kind)
	}
	if aux != "" && !validAuxType(info.AuxType) {
		return nil, nil, fmt.Errorf("block %s has no aux", kind)
	}
	b := &Block{Text: s, Kind: kind, Info: info, Type: typ, AuxInt: auxint, Aux: aux}
	return b, args, nil
}

func validAuxType(t string) bool { return t != "" && t != "invalid" }

// checkEllipsis enforces rulegen's restrictions on "..." rules,
// which must have the form (Op ...) => (Op2 ...).
func checkEllipsis(r *Rule) error {
	if !strings.Contains(r.Text, "...") {
		return nil
	}
	plain := func(v *Value) bool {
		return v != nil && v.Ellipsis && v.Type == "" && v.AuxInt == "" && v.Aux == "" && v.Name == ""
	}
	if r.Cond != "" || r.Placement != "" || !plain(r.Match) || !plain(r.Result) {
		return errors.New("found ellipsis in non-ellipsis rule")
	}
	if r.Match.Op.Aux != r.Result.Op.Aux {
		return fmt.Errorf("can't use ... for ops that have different aux types: %s and %s", r.Match.Op, r.Result.Op)
	}
	return nil
}

// checkMatchNames rejects match-side names that generated code
// cannot declare.
func (p *ruleParser) checkMatchNames(r *Rule) error {
	var err error
	check := func(name string) {
		if err == nil && p.arch.Tables().ReservedNames[name] {
			err = fmt.Errorf("rule uses the reserved name %s", name)
		}
	}
	for _, o := range r.MatchOccurrences() {
		check(o.Name)
	}
	return err
}
