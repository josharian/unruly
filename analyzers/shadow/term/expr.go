package term

import (
	"bytes"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/printer"
	"go/scanner"
	"go/token"
	"go/types"
	"strings"
	"sync"
)

// This file holds helpers for the Go expressions in rules, which this
// package handles as canonical text: the go/printer form of the parsed
// expression.

var (
	parseMu    sync.Mutex
	parseCache = map[string]ast.Expr{}
	evalCache  = map[string]constant.Value{}
)

// parse parses s, returning nil if it is not a Go expression.
// The result is shared; don't modify it.
func parse(s string) ast.Expr {
	parseMu.Lock()
	defer parseMu.Unlock()
	if x, ok := parseCache[s]; ok {
		return x
	}
	x, err := parser.ParseExpr(s)
	if err != nil {
		x = nil
	}
	parseCache[s] = x
	return x
}

// Canon returns the canonical text of Go expression s,
// or s with whitespace collapsed if it does not parse.
func Canon(s string) string {
	x := parse(s)
	if x == nil {
		return strings.Join(strings.Fields(s), " ")
	}
	return format(x)
}

func format(x ast.Expr) string {
	var buf bytes.Buffer
	printer.Fprint(&buf, token.NewFileSet(), x)
	return buf.String()
}

// Subst returns the canonical text of expression s with each identifier
// that is not a field or method name replaced by repl(name), if repl
// reports true. A replacement that is not an identifier or literal is
// parenthesized.
func Subst(s string, repl func(name string) (string, bool)) string {
	var sc scanner.Scanner
	fset := token.NewFileSet()
	src := []byte(s)
	sc.Init(fset.AddFile("", -1, len(src)), src, nil, 0)
	var out strings.Builder
	prev := token.ILLEGAL
	for {
		_, tok, lit := sc.Scan()
		if tok == token.EOF {
			break
		}
		if tok == token.SEMICOLON && lit == "\n" {
			continue
		}
		text := lit
		if text == "" {
			text = tok.String()
		}
		if tok == token.IDENT && prev != token.PERIOD {
			if r, ok := repl(lit); ok {
				text = r
				if !token.IsIdentifier(r) && !isLiteral(r) {
					text = "(" + r + ")"
				}
			}
		}
		out.WriteString(text)
		out.WriteByte(' ')
		prev = tok
	}
	return Canon(out.String())
}

func isLiteral(s string) bool {
	if s == "" {
		return false
	}
	c := s[0]
	return c >= '0' && c <= '9' || c == '"' || c == '\''
}

// Idents returns the identifiers in s that are not field or method names.
func Idents(s string) []string {
	var ids []string
	Subst(s, func(name string) (string, bool) {
		ids = append(ids, name)
		return "", false
	})
	return ids
}

// Eval returns the constant value of s, or nil if it is not constant
// using only Go's predeclared identifiers.
func Eval(s string) constant.Value {
	parseMu.Lock()
	v, ok := evalCache[s]
	parseMu.Unlock()
	if ok {
		return v
	}
	tv, err := types.Eval(token.NewFileSet(), nil, token.NoPos, s)
	if err == nil && tv.Value != nil {
		v = tv.Value
	}
	parseMu.Lock()
	evalCache[s] = v
	parseMu.Unlock()
	return v
}

// Fold returns the canonical text of s, with s replaced by its value
// if it is constant.
func Fold(s string) string {
	if v := Eval(s); v != nil {
		return v.ExactString()
	}
	return Canon(s)
}

// SameExpr reports whether Go expressions a and b certainly have the same
// value: they are textually identical or equal constants.
func SameExpr(a, b string) bool {
	if Canon(a) == Canon(b) {
		return true
	}
	va, vb := Eval(a), Eval(b)
	return va != nil && vb != nil && va.Kind() == vb.Kind() && constant.Compare(va, token.EQL, vb)
}

// DiffExpr reports whether Go expressions a and b certainly have different
// values: they are unequal constants.
func DiffExpr(a, b string) bool {
	va, vb := Eval(a), Eval(b)
	return va != nil && vb != nil && va.Kind() == vb.Kind() && !constant.Compare(va, token.EQL, vb)
}

// Conjuncts splits s at its top-level && operators.
func Conjuncts(s string) []string {
	if s == "" {
		return nil
	}
	x := parse(s)
	if x == nil {
		return []string{Canon(s)}
	}
	var out []string
	var walk func(x ast.Expr)
	walk = func(x ast.Expr) {
		if p, ok := x.(*ast.ParenExpr); ok {
			walk(p.X)
			return
		}
		if b, ok := x.(*ast.BinaryExpr); ok && b.Op == token.LAND {
			walk(b.X)
			walk(b.Y)
			return
		}
		out = append(out, format(x))
	}
	walk(x)
	return out
}
