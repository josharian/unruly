// Portions of this file are adapted from Go's
// cmd/compile/internal/ssa/_gen/rulegen.go.
//
// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the GOLICENSE file.

package rules

import (
	"bufio"
	"bytes"
	"fmt"
	"regexp"
	"strings"
)

// This file holds rulegen's string-level syntax handling, kept as close to
// rulegen's code as possible so that the AST faithfully reflects how rulegen
// reads rules, quirks included.

// rawRule is a rule's text as accumulated from one or more source lines.
type rawRule struct {
	start, end int // first and last line
	text       string
}

// scanRules splits src into rules the way rulegen's genRulesSuffix does:
// comments ("//" to end of line, even inside strings) are removed, and
// lines accumulate until the text contains "=>", does not end with "=>",
// and has balanced parentheses.
func scanRules(path string, src []byte) ([]rawRule, []error) {
	var rules []rawRule
	var errs []error
	scanner := bufio.NewScanner(bytes.NewReader(src))
	rule := ""
	start := 0
	lineno := 0
	for scanner.Scan() {
		lineno++
		line := scanner.Text()
		if i := strings.Index(line, "//"); i >= 0 {
			line = line[:i]
		}
		rule += " " + line
		rule = strings.TrimSpace(rule)
		if rule == "" {
			continue
		}
		if start == 0 {
			start = lineno
		}
		if !strings.Contains(rule, "=>") {
			if strings.Contains(rule, "->") && balance(rule) == 0 {
				errs = append(errs, &Error{Pos{path, start}, "untyped -> rules are not supported"})
				rule, start = "", 0
			}
			continue
		}
		if strings.HasSuffix(rule, "=>") {
			continue // continue on the next line
		}
		if n := balance(rule); n > 0 {
			continue // open parentheses remain, continue on the next line
		} else if n < 0 {
			errs = append(errs, &Error{Pos{path, start}, "unbalanced rule: " + rule})
			rule, start = "", 0
			continue
		}
		rules = append(rules, rawRule{start: start, end: lineno, text: rule})
		rule, start = "", 0
	}
	if err := scanner.Err(); err != nil {
		errs = append(errs, fmt.Errorf("%s: %v", path, err))
	}
	if rule != "" {
		msg := "incomplete rule at end of file: "
		if balance(rule) != 0 {
			msg = "unbalanced rule: "
		}
		errs = append(errs, &Error{Pos{path, start}, msg + rule})
	}
	return rules, errs
}

func normalizeSpaces(s string) string {
	return strings.Join(strings.Fields(strings.TrimSpace(s)), " ")
}

// balance returns the number of unclosed '(' characters in s.
// If a ')' appears without a corresponding '(', balance returns -1.
func balance(s string) int {
	balance := 0
	for _, c := range s {
		switch c {
		case '(':
			balance++
		case ')':
			balance--
			if balance < 0 {
				// don't allow ")(" to return 0
				return -1
			}
		}
	}
	return balance
}

// split splits s at spaces and tabs, except those inside (), {}, [], or <>
// or following a colon. Like rulegen's split, it tracks nesting only of the
// bracket kind that opened the current element.
func split(s string) ([]string, error) {
	var r []string

outer:
	for s != "" {
		d := 0               // depth of ({[<
		var open, close byte // opening and closing markers ({[< or )}]>
		nonsp := false       // found a non-space char so far
		for i := 0; i < len(s); i++ {
			switch {
			case d == 0 && s[i] == '(':
				open, close = '(', ')'
				d++
			case d == 0 && s[i] == '<':
				open, close = '<', '>'
				d++
			case d == 0 && s[i] == '[':
				open, close = '[', ']'
				d++
			case d == 0 && s[i] == '{':
				open, close = '{', '}'
				d++
			case d == 0 && (s[i] == ' ' || s[i] == '\t'):
				if nonsp {
					r = append(r, strings.TrimSpace(s[:i]))
					s = s[i:]
					continue outer
				}
			case d > 0 && s[i] == open:
				d++
			case d > 0 && s[i] == close:
				d--
			case s[i] == ':':
				// ignore spaces after colons
				nonsp = true
				for i+1 < len(s) && (s[i+1] == ' ' || s[i+1] == '\t') {
					i++
				}
			default:
				nonsp = true
			}
		}
		if d != 0 {
			return nil, fmt.Errorf("imbalanced expression: %q", s)
		}
		if nonsp {
			r = append(r, strings.TrimSpace(s))
		}
		break
	}
	return r, nil
}

// extract splits a parenthesized s-expression into its op, type, auxint,
// aux, and args. rulegen silently keeps the last of repeated <>, [], or {}
// parts; extract reports them as an error.
func extract(val string) (op, typ, auxint, aux string, args []string, err error) {
	if len(val) < 2 || val[0] != '(' || val[len(val)-1] != ')' {
		return "", "", "", "", nil, fmt.Errorf("expected parenthesized s-expression, found %q", val)
	}
	s, err := split(val[1 : len(val)-1])
	if err != nil {
		return "", "", "", "", nil, err
	}
	if len(s) == 0 {
		return "", "", "", "", nil, fmt.Errorf("empty s-expression %q", val)
	}
	op = s[0]
	var seenTyp, seenAuxInt, seenAux bool
	dup := func(seen *bool, what string) {
		if *seen && err == nil {
			err = fmt.Errorf("repeated %s in %q", what, val)
		}
		*seen = true
	}
	for _, a := range s[1:] {
		switch a[0] {
		case '<':
			dup(&seenTyp, "<type>")
			typ = a[1 : len(a)-1] // remove <>
		case '[':
			dup(&seenAuxInt, "[auxint]")
			auxint = a[1 : len(a)-1] // remove []
		case '{':
			dup(&seenAux, "{aux}")
			aux = a[1 : len(a)-1] // remove {}
		default:
			args = append(args, a)
		}
	}
	return op, typ, auxint, aux, args, err
}

// splitNameExpr splits s-expr arg, possibly prefixed by "name:",
// into name and the unprefixed expression.
// For example, "x:(Foo)" yields "x", "(Foo)",
// and "(Foo)" yields "", "(Foo)".
func splitNameExpr(arg string) (name, expr string, err error) {
	colon := strings.Index(arg, ":")
	if colon < 0 {
		return "", arg, nil
	}
	openparen := strings.Index(arg, "(")
	if openparen < 0 {
		return "", "", fmt.Errorf("%q: colon but no open parens", arg)
	}
	if colon > openparen {
		// colon is inside the parens, such as in "(Foo x:(Bar))".
		return "", arg, nil
	}
	return arg[:colon], strings.TrimSpace(arg[colon+1:]), nil
}

// findAllOpcode finds the |-alternations in a rule, such as "(B|W|L|Q)".
var findAllOpcode = regexp.MustCompile(`[(](\w+[|])+\w+[)]`).FindAllStringIndex

// excludeFromExpansion reports whether the substring s[idx[0]:idx[1]] in a rule
// should be disregarded as a candidate for | expansion.
// It uses simple syntactic checks to see whether the substring
// is inside an AuxInt expression or inside the && conditions.
func excludeFromExpansion(s string, idx []int) bool {
	left := s[:idx[0]]
	if strings.LastIndexByte(left, '[') > strings.LastIndexByte(left, ']') {
		// Inside an AuxInt expression.
		return true
	}
	right := s[idx[1]:]
	if strings.Contains(left, "&&") && strings.Contains(right, "=>") {
		// Inside && conditions.
		return true
	}
	return false
}

// expandOr converts a rule into multiple rules by expanding | alternations.
// All alternations in a rule must have the same width; the i'th expansion
// selects the i'th alternative of each.
func expandOr(r string) ([]string, error) {
	n := 1
	for _, idx := range findAllOpcode(r, -1) {
		if excludeFromExpansion(r, idx) {
			continue
		}
		s := r[idx[0]:idx[1]]
		c := strings.Count(s, "|") + 1
		if c == 1 {
			continue
		}
		if n > 1 && n != c {
			return nil, fmt.Errorf("'|' count doesn't match: both %d and %d", n, c)
		}
		n = c
	}
	if n == 1 {
		// No |-form in this rule.
		return []string{r}, nil
	}
	res := make([]string, n)
	for i := range n {
		buf := new(strings.Builder)
		x := 0
		for _, idx := range findAllOpcode(r, -1) {
			if excludeFromExpansion(r, idx) {
				continue
			}
			buf.WriteString(r[x:idx[0]])              // write bytes we've skipped over so far
			s := r[idx[0]+1 : idx[1]-1]               // remove leading "(" and trailing ")"
			buf.WriteString(strings.Split(s, "|")[i]) // write the op component for this rule
			x = idx[1]                                // note that we've written more bytes
		}
		buf.WriteString(r[x:])
		res[i] = buf.String()
	}
	return res, nil
}
