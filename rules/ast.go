// Package rules parses the Go compiler's SSA rewrite rules (*.rules files)
// into an AST, resolving ops against op tables the way rulegen does.
//
// A rule has the form
//
//	match [&& cond] => [@block] result
//
// Value rules match and produce values: (Add64 x (Const64 [0])) => x.
// Block rules match and produce blocks: (If (Not cond) yes no) => (If cond no yes).
package rules

import (
	"fmt"
	"go/ast"
	"go/token"

	"github.com/josharian/unruly/ops"
)

// Pos is a source position: a rules file and a 1-based line number.
type Pos struct {
	File string
	Line int
}

func (p Pos) String() string { return fmt.Sprintf("%s:%d", p.File, p.Line) }

// Error is a parse error.
type Error struct {
	Pos Pos
	Msg string
}

func (e *Error) Error() string { return e.Pos.String() + ": " + e.Msg }

// File is a parsed rules file.
type File struct {
	Path  string
	Rules []*Rule // in source order, with | alternations expanded
}

// Rule is one rule, after | alternation expansion.
//
// A value rule has Match set and exactly one of Result or ResultCode.
// A block rule has MatchBlock and ResultBlock set.
type Rule struct {
	Pos     Pos // the rule's first line
	EndLine int // the rule's last line
	File    *File
	Set     *RuleSet

	// Orig is the rule as written, before | expansion (comments removed,
	// whitespace normalized). Text is this expansion of it: the NumAlts
	// expansions of Orig appear consecutively, with Alt numbering them
	// from 0. NumAlts is 1 if Orig contains no alternation.
	Orig    string
	Text    string
	Alt     int
	NumAlts int

	// MatchText, Cond, and ResultText are the three parts of Text,
	// whitespace-normalized, exactly as rulegen splits them (they appear as
	// the "match:", "cond:", and "result:" comments in generated code).
	// Cond is "" if the rule has no condition.
	MatchText  string
	Cond       string
	ResultText string

	// CondExpr is Cond parsed as a Go expression, or nil.
	// Its positions are relative to Cond, not to the rules file.
	CondExpr ast.Expr

	Match  *Value
	Result *Value
	// ResultCode is the Go expression of a {code} result, without braces.
	// rulegen generates v.copyOf(code).
	ResultCode string
	// Placement is the block expression of an @block result, such as
	// "x.Block", or "".
	Placement string

	MatchBlock  *Block
	ResultBlock *Block
}

// IsBlock reports whether r is a block rule.
func (r *Rule) IsBlock() bool { return r.MatchBlock != nil }

func (r *Rule) String() string { return r.Text }

// Value is an s-expression denoting a value, or a leaf.
//
// A compound value (Op != nil) is written [name:](Op <type> [auxint] {aux} args...).
// A leaf (Op == nil) is written name. In a match, a leaf is a variable or _.
// In a result, a leaf is any Go expression: usually a variable bound by the
// match, but possibly something like x.Args[0] or f(v).
type Value struct {
	// Text is the s-expression as rulegen sees it, without any "name:" prefix.
	// For a leaf, it equals Name.
	Text string

	// Name is the variable this node binds (x in x:(Op ...)), or "" if none.
	// For a leaf, Name is the leaf's text.
	Name string

	OpName string  // as written; "" for a leaf
	Op     *ops.Op // the resolved op; nil for a leaf

	// Type, AuxInt, and Aux are the contents of <...>, [...], and {...},
	// or "" if absent. In a match they are variables to bind or Go
	// expressions to compare against (see Rule.Constraints); in a result
	// they are Go expressions.
	Type   string
	AuxInt string
	Aux    string

	Args []*Value

	// Ellipsis reports that the args were written "...": (Op ...).
	// Args is then empty. See Rule.IsEllipsis.
	Ellipsis bool
	// Rest reports a trailing "___" (not included in Args), allowed in
	// matches of variadic ops: the value has at least len(Args) args.
	Rest bool
}

// IsLeaf reports whether v is a leaf (variable or Go expression).
func (v *Value) IsLeaf() bool { return v.Op == nil }

// IsVar reports whether v is a leaf naming a variable (not _ and not
// a more complex Go expression).
func (v *Value) IsVar() bool {
	return v.Op == nil && v.Name != "_" && token.IsIdentifier(v.Name)
}

func (v *Value) String() string { return v.Text }

// Walk calls f for v and, if f returns true, for each of v's args, recursively.
func (v *Value) Walk(f func(*Value) bool) {
	if !f(v) {
		return
	}
	for _, a := range v.Args {
		a.Walk(f)
	}
}

// Block is a block s-expression: (Kind <type> [auxint] {aux} controls... succs...).
type Block struct {
	Text   string
	Kind   string     // as written
	Info   *ops.Block // resolved
	Type   string     // ignored by rulegen
	AuxInt string
	Aux    string

	Controls []*Value // len(Controls) == Info.Controls
	Succs    []string // successor names, such as "yes" and "no"
}

func (b *Block) String() string { return b.Text }

// MatchValues returns the top-level values of r's match side:
// the match value of a value rule, or the controls of a block rule.
func (r *Rule) MatchValues() []*Value {
	if r.IsBlock() {
		return r.MatchBlock.Controls
	}
	return []*Value{r.Match}
}

// ResultValues returns the top-level values of r's result side: the result
// value of a value rule (none for a {code} result), or the controls of a
// block rule.
func (r *Rule) ResultValues() []*Value {
	if r.IsBlock() {
		return r.ResultBlock.Controls
	}
	if r.Result == nil {
		return nil
	}
	return []*Value{r.Result}
}
