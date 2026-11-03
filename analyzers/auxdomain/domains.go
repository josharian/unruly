package auxdomain

import (
	"bufio"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"sync"
)

// A domain is the range of auxints an op accepts, and where it says so.
type domain struct {
	lo, hi int64
	src    string // file:line of the documentation
}

// domains returns the auxint domains of arch's ops, as documented in
// <arch>Ops.go. An op's domain comes from its own line comment, such as
//
//	{name: "SLLVconst", ..., aux: "Int64"}, // arg0 << auxInt, auxInt should be in the range 0 to 63.
//	{name: "SRWconst", ..., aux: "Int64"},  // unsigned arg0 >> auxInt, 0 <= auxInt < 32, 32 bit width
//	{name: "SLDconst", ..., aux: "UInt8"},  // arg0 << auxint, shift amount 0-63
//
// or from a comment line that states the range for the ops after it, up
// to the next comment line that follows an op:
//
//	// auxInt for all of these satisfy 0 <= auxInt < 32
//	// ... auxint must be in the range 0 to (Q=63,L=31,W=15,B=7) inclusive.
//
// In the second form, an op named <x>Qconst gets [0, 63], and so on.
func domains(genDir, arch string) map[string]domain {
	key := genDir + "\x00" + arch
	if m, ok := domainCache.Load(key); ok {
		return m.(map[string]domain)
	}
	m := loadDomains(filepath.Join(genDir, arch+"Ops.go"))
	domainCache.Store(key, m)
	return m
}

var domainCache sync.Map

var (
	opLine = regexp.MustCompile(`^\s*\{name:\s*"(\w+)"`)
	ranges = []*regexp.Regexp{
		regexp.MustCompile(`(?i)(\d+)\s*<=\s*auxint\s*<\s*(\d+)`),                                    // [a, b)
		regexp.MustCompile(`(?i)(?:shift|rotate) amount (?:must be )?(\d+)\s*(?:-|through)\s*(\d+)`), // [a, b]
		regexp.MustCompile(`(?i)auxint should be in the range (\d+) to (\d+)`),                       // [a, b]
		regexp.MustCompile(`(?i)value of auxint should be in the range \[(\d+),\s*(\d+)\]`),          // [a, b]
	}
	suffixed = regexp.MustCompile(`(?i)auxint must be in the range 0 to \(Q=(\d+),L=(\d+),W=(\d+),B=(\d+)\)`)
)

// parseRange returns the range that comment states.
func parseRange(comment string) (lo, hi int64, ok bool) {
	for i, re := range ranges {
		m := re.FindStringSubmatch(comment)
		if m == nil {
			continue
		}
		lo, _ = strconv.ParseInt(m[1], 10, 64)
		hi, _ = strconv.ParseInt(m[2], 10, 64)
		if i == 0 {
			hi--
		}
		return lo, hi, true
	}
	return 0, 0, false
}

func loadDomains(path string) map[string]domain {
	m := map[string]domain{}
	f, err := os.Open(path)
	if err != nil {
		return m
	}
	defer f.Close()
	base := filepath.Base(path)

	// The range stated by the current block of comment lines.
	var group func(op string) (int64, int64, bool)
	groupSrc := ""
	seenOp := false

	sc := bufio.NewScanner(f)
	for n := 1; sc.Scan(); n++ {
		line := sc.Text()
		trimmed := strings.TrimSpace(line)
		if strings.HasPrefix(trimmed, "//") {
			if seenOp {
				group, seenOp = nil, false
			}
			if lo, hi, ok := parseRange(trimmed); ok {
				group = func(string) (int64, int64, bool) { return lo, hi, true }
				groupSrc = base + ":" + strconv.Itoa(n)
			} else if s := suffixed.FindStringSubmatch(trimmed); s != nil {
				var hi [4]int64
				for i := range hi {
					hi[i], _ = strconv.ParseInt(s[i+1], 10, 64)
				}
				group = func(op string) (int64, int64, bool) {
					name, ok := strings.CutSuffix(op, "const")
					if !ok || name == "" {
						return 0, 0, false
					}
					i := strings.IndexByte("QLWB", name[len(name)-1])
					if i < 0 {
						return 0, 0, false
					}
					return 0, hi[i], true
				}
				groupSrc = base + ":" + strconv.Itoa(n)
			}
			continue
		}
		om := opLine.FindStringSubmatch(line)
		if om == nil {
			continue
		}
		seenOp = true
		op := om[1]
		if _, comment, ok := strings.Cut(line, "//"); ok {
			if lo, hi, ok := parseRange(comment); ok {
				m[op] = domain{lo, hi, base + ":" + strconv.Itoa(n)}
				continue
			}
		}
		if group != nil {
			if lo, hi, ok := group(op); ok {
				m[op] = domain{lo, hi, groupSrc}
			}
		}
	}
	return m
}

// A regShift is how a shift or rotate by a register uses its count, as
// documented in <arch>Ops.go.
type regShift struct {
	kind shiftKind
	mod  int64  // the count is used modulo mod
	src  string // file:line of the documentation
}

type shiftKind int8

const (
	shiftLeft       shiftKind = iota // x << k; 0 if k >= width
	shiftRight                       // logical x >> k; 0 if k >= width
	shiftRightArith                  // arithmetic x >> k; as k = width-1 if k >= width
	rotate                           // rotate by k mod width
)

func (k shiftKind) String() string {
	return [...]string{"<<", ">>", ">>", "rotate"}[k]
}

// regShifts returns how arch's register shift and rotate ops use their
// counts, from comments such as
//
//	{name: "SLL", ...}, // arg0 << arg1, shift amount is mod 256
//	{name: "SLD", ...}, // arg0 << (arg1&127), 64 bit width
//	{name: "SRA", ...}, // arg0 >> (aux1 & 63), arithmetic right shift
//	{name: "ROR", ...}, // arg0 right rotate by (arg1 mod 64) bits
//	// arg1 is the amount to shift, interpreted mod (Q=64,L=32,W=32,B=32)
func regShifts(genDir, arch string) map[string]regShift {
	key := genDir + "\x00" + arch
	if m, ok := regShiftCache.Load(key); ok {
		return m.(map[string]regShift)
	}
	m := loadRegShifts(filepath.Join(genDir, arch+"Ops.go"))
	regShiftCache.Store(key, m)
	return m
}

var regShiftCache sync.Map

var (
	modRanges = []*regexp.Regexp{
		regexp.MustCompile(`shift amount is mod (\d+)`),       // N
		regexp.MustCompile(`\(arg1 mod (\d+)\)`),              // N
		regexp.MustCompile(`\((?:arg1|aux1)\s*&\s*(\d+)\)`),   // N-1
		regexp.MustCompile(`(?:rotate|shift) amount 0-(\d+)`), // N-1
	}
	modSuffixed = regexp.MustCompile(`interpreted mod \(Q=(\d+),L=(\d+),W=(\d+),B=(\d+)\)`)
)

func loadRegShifts(path string) map[string]regShift {
	m := map[string]regShift{}
	f, err := os.Open(path)
	if err != nil {
		return m
	}
	defer f.Close()
	base := filepath.Base(path)
	var group []int64 // moduli for Q, L, W, B, from a comment block
	groupSrc := ""
	seenOp := false
	sc := bufio.NewScanner(f)
	for n := 1; sc.Scan(); n++ {
		line := sc.Text()
		if strings.HasPrefix(strings.TrimSpace(line), "//") {
			if seenOp {
				group, seenOp = nil, false
			}
			if s := modSuffixed.FindStringSubmatch(line); s != nil {
				group = nil
				for _, x := range s[1:] {
					v, _ := strconv.ParseInt(x, 10, 64)
					group = append(group, v)
				}
				groupSrc = base + ":" + strconv.Itoa(n)
			}
			continue
		}
		om := opLine.FindStringSubmatch(line)
		if om == nil || !strings.Contains(line, "argLength: 2") {
			continue
		}
		seenOp = true
		op := om[1]
		_, comment, _ := strings.Cut(line, "//")
		if mod, ok := parseMod(comment); ok {
			if k, ok := commentKind(op, comment); ok {
				m[op] = regShift{k, mod, base + ":" + strconv.Itoa(n)}
			}
			continue
		}
		if group != nil && len(op) > 3 {
			i := strings.IndexByte("QLWB", op[len(op)-1])
			k, ok := prefixKind(op)
			if i >= 0 && ok {
				m[op] = regShift{k, group[i], groupSrc}
			}
		}
	}
	return m
}

func parseMod(comment string) (int64, bool) {
	for i, re := range modRanges {
		s := re.FindStringSubmatch(comment)
		if s == nil {
			continue
		}
		v, _ := strconv.ParseInt(s[1], 10, 64)
		if i >= 2 {
			v++
		}
		return v, v > 0 && v&(v-1) == 0
	}
	return 0, false
}

func commentKind(op, c string) (shiftKind, bool) {
	switch {
	case strings.HasPrefix(op, "SRA") || strings.HasPrefix(op, "SAR"):
		return shiftRightArith, true
	case strings.Contains(c, "rotate"):
		return rotate, true
	case strings.Contains(c, "<<"):
		return shiftLeft, true
	case strings.Contains(c, ">>"):
		if strings.Contains(c, "arithmetic") || strings.Contains(c, "signed") && !strings.Contains(c, "unsigned") {
			return shiftRightArith, true
		}
		return shiftRight, true
	}
	return 0, false
}

// prefixKind returns the kind of an x86 shift or rotate op from its name.
func prefixKind(op string) (shiftKind, bool) {
	switch op[:3] {
	case "SHL":
		return shiftLeft, true
	case "SHR":
		return shiftRight, true
	case "SAR":
		return shiftRightArith, true
	case "ROL":
		return rotate, true
	}
	return 0, false
}
