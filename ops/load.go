package ops

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"sync"
)

// FindGenDir returns the rulegen directory for path, which may be a Go root
// (containing src/cmd/compile/internal/ssa/_gen or, in older trees, .../gen)
// or the _gen directory itself.
func FindGenDir(path string) (string, error) {
	if isGenDir(path) {
		return path, nil
	}
	for _, sub := range []string{"_gen", "gen"} {
		dir := filepath.Join(path, "src", "cmd", "compile", "internal", "ssa", sub)
		if isGenDir(dir) {
			return dir, nil
		}
	}
	return "", fmt.Errorf("%s is neither a Go root nor an SSA _gen directory", path)
}

func isGenDir(dir string) bool {
	_, err := os.Stat(filepath.Join(dir, "genericOps.go"))
	return err == nil
}

var memo struct {
	sync.Mutex
	m map[string]*Tables // by content key
}

// Load returns the op tables for the _gen directory dir.
//
// The first load of a given set of _gen Go sources builds and runs a program
// (requiring the go command), which takes a few seconds. The result is
// cached in the user cache directory, keyed by the content of those sources.
func Load(dir string) (*Tables, error) {
	dir, err := filepath.Abs(dir)
	if err != nil {
		return nil, err
	}
	key, err := contentKey(dir)
	if err != nil {
		return nil, err
	}
	// Tables.Dir locates the rest of the tree (codegen, rewrite helpers),
	// which can differ between trees with identical _gen sources.
	// So the in-memory cache, unlike the content-keyed disk cache,
	// is per directory.
	memoKey := key + "\x00" + dir
	memo.Lock()
	defer memo.Unlock()
	if t := memo.m[memoKey]; t != nil {
		return t, nil
	}

	var data []byte
	cacheFile := ""
	if cd, err := os.UserCacheDir(); err == nil {
		cacheFile = filepath.Join(cd, "unruly", "ops", key+".json")
		data, _ = os.ReadFile(cacheFile)
	}
	if data == nil {
		data, err = dump(dir)
		if err != nil {
			return nil, err
		}
		if cacheFile != "" {
			writeCache(cacheFile, data)
		}
	}
	t, err := decode(data)
	if err != nil {
		return nil, fmt.Errorf("decoding op dump of %s: %v", dir, err)
	}
	t.Dir = dir
	if memo.m == nil {
		memo.m = make(map[string]*Tables)
	}
	memo.m[memoKey] = t
	return t, nil
}

func writeCache(file string, data []byte) {
	if err := os.MkdirAll(filepath.Dir(file), 0o777); err != nil {
		return
	}
	tmp, err := os.CreateTemp(filepath.Dir(file), "tmp-")
	if err != nil {
		return
	}
	_, err = tmp.Write(data)
	if cerr := tmp.Close(); err == nil {
		err = cerr
	}
	if err == nil {
		err = os.Rename(tmp.Name(), file)
	}
	if err != nil {
		os.Remove(tmp.Name())
	}
}

// contentKey hashes the Go sources of dir.
func contentKey(dir string) (string, error) {
	names, err := genGoFiles(dir)
	if err != nil {
		return "", err
	}
	h := sha256.New()
	h.Write(dumpSource)
	for _, name := range names {
		b, err := os.ReadFile(filepath.Join(dir, name))
		if err != nil {
			return "", err
		}
		fmt.Fprintf(h, "%s %d\n", name, len(b))
		h.Write(b)
	}
	return hex.EncodeToString(h.Sum(nil))[:32], nil
}

type dumpData struct {
	Archs             []map[string]any
	GenericOps        []map[string]any
	GenericBlocks     []map[string]any
	GenericOpExtra    []map[string]any
	GenericBlockExtra []map[string]any
	OpExtra           [][]map[string]any
	BlockExtra        [][]map[string]any
	ReservedNames     map[string]bool
	SIMDGenericOps    []string
}

func decode(data []byte) (*Tables, error) {
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.UseNumber()
	var d dumpData
	if err := dec.Decode(&d); err != nil {
		return nil, err
	}
	t := &Tables{byName: make(map[string]*Arch), ReservedNames: d.ReservedNames}
	for i, raw := range d.Archs {
		a := decodeArch(raw)
		a.tables = t
		rawOps, _ := raw["ops"].([]any)
		rawBlocks, _ := raw["blocks"].([]any)
		var opExtra, blockExtra []map[string]any
		if i < len(d.OpExtra) {
			opExtra = d.OpExtra[i]
		}
		if i < len(d.BlockExtra) {
			blockExtra = d.BlockExtra[i]
		}
		if a.Name == "generic" {
			// rulegen consults the genericOps and genericBlocks
			// globals, not the generic arch's fields.
			if d.GenericOps != nil {
				rawOps, opExtra = anys(d.GenericOps), d.GenericOpExtra
			}
			if d.GenericBlocks != nil {
				rawBlocks, blockExtra = anys(d.GenericBlocks), d.GenericBlockExtra
			}
		}
		for j, r := range rawOps {
			op := decodeOp(asMap(r), extraAt(opExtra, j))
			op.Arch = a
			a.Ops = append(a.Ops, op)
		}
		for j, r := range rawBlocks {
			b := decodeBlock(asMap(r), extraAt(blockExtra, j))
			b.Arch = a
			a.Blocks = append(a.Blocks, b)
		}
		if t.byName[a.Name] != nil {
			return nil, fmt.Errorf("duplicate arch %s", a.Name)
		}
		t.byName[a.Name] = a
		t.Archs = append(t.Archs, a)
	}
	t.Generic = t.byName["generic"]
	if t.Generic == nil {
		return nil, errors.New("no generic arch")
	}
	simd := make(map[string]bool)
	for _, name := range d.SIMDGenericOps {
		simd[name] = true
	}
	for _, op := range t.Generic.Ops {
		op.SIMD = simd[op.Name]
	}
	slices.SortFunc(t.Archs, func(a, b *Arch) int { return strings.Compare(a.Name, b.Name) })
	for _, a := range t.Archs {
		a.index()
	}
	return t, nil
}

func (a *Arch) index() {
	a.opIdx = make(map[string]*Op)
	for _, op := range a.Ops {
		if _, dup := a.opIdx[op.Name]; !dup {
			a.opIdx[op.Name] = op
		}
	}
	a.blkIdx = make(map[string]*Block)
	for _, b := range a.Blocks {
		if _, dup := a.blkIdx[b.Name]; !dup {
			a.blkIdx[b.Name] = b
		}
	}
	a.regIdx = make(map[string]int)
	for i, r := range a.RegNames {
		a.regIdx[r] = i
	}
	a.classes = []classMask{
		{RegGP, a.GPRegMask},
		{RegFP, a.FPRegMask.Union(a.FP32RegMask).Union(a.FP64RegMask)},
		{RegSIMD, a.SIMDRegMask},
		{RegSIMDMask, a.SIMDMaskRegs},
	}
}

func decodeArch(m map[string]any) *Arch {
	a := &Arch{
		Name:           str(m, "name"),
		Generic:        boolean(m, "generic"),
		Pkg:            str(m, "pkg"),
		GPRegMask:      regMask(m["gpregmask"]),
		FPRegMask:      regMask(m["fpregmask"]),
		FP32RegMask:    regMask(m["fp32regmask"]),
		FP64RegMask:    regMask(m["fp64regmask"]),
		SIMDRegMask:    regMask(m["simdregmask"]),
		SIMDMaskRegs:   regMask(m["simdmaskreg"]),
		SpecialRegMask: regMask(m["specialregmask"]),
		FramePointer:   -1,
		LinkReg:        -1,
		Raw:            make(map[string]any),
	}
	if _, ok := m["framepointerreg"]; ok {
		a.FramePointer = int(integer(m, "framepointerreg"))
	}
	if _, ok := m["linkreg"]; ok {
		a.LinkReg = int(integer(m, "linkreg"))
	}
	for _, r := range anys(m["regnames"]) {
		s, _ := r.(string)
		a.RegNames = append(a.RegNames, s)
	}
	for k, v := range m {
		if k != "ops" && k != "blocks" {
			a.Raw[k] = v
		}
	}
	return a
}

func decodeOp(m, extra map[string]any) *Op {
	op := &Op{
		Name:              str(m, "name"),
		Asm:               str(m, "asm"),
		Typ:               str(m, "typ"),
		Aux:               str(m, "aux"),
		ArgLength:         int32(integer(m, "argLength")),
		Rematerializeable: boolean(m, "rematerializeable"),
		Commutative:       boolean(m, "commutative"),
		ResultInArg0:      boolean(m, "resultInArg0"),
		ResultNotInArgs:   boolean(m, "resultNotInArgs"),
		ClobberFlags:      boolean(m, "clobberFlags"),
		NeedIntTemp:       boolean(m, "needIntTemp"),
		Call:              boolean(m, "call"),
		TailCall:          boolean(m, "tailCall"),
		NilCheck:          boolean(m, "nilCheck"),
		FaultOnNilArg0:    boolean(m, "faultOnNilArg0"),
		FaultOnNilArg1:    boolean(m, "faultOnNilArg1"),
		HasSideEffects:    boolean(m, "hasSideEffects"),
		ZeroWidth:         boolean(m, "zeroWidth"),
		UnsafePoint:       boolean(m, "unsafePoint"),
		FixedReg:          boolean(m, "fixedReg"),
		EarlyOk:           boolean(m, "earlyOk"),
		AddrSinkArg0:      boolean(m, "addrSinkArg0"),
		AddrSinkArg1:      boolean(m, "addrSinkArg1"),
		SymEffect:         str(m, "symEffect"),
		Scale:             uint8(integer(m, "scale")),
		ZeroUpperBits:     uint8(integer(m, "zeroUpperBits")),
		AuxType:           str(extra, "auxType"),
		AuxIntType:        str(extra, "auxIntType"),
		HasAux:            boolean(extra, "hasAux"),
		HasAuxInt:         boolean(extra, "hasAuxInt"),
		Raw:               m,
	}
	if reg := asMap(m["reg"]); reg != nil {
		for _, r := range anys(reg["inputs"]) {
			op.Reg.Inputs = append(op.Reg.Inputs, regMask(r))
		}
		for _, r := range anys(reg["outputs"]) {
			op.Reg.Outputs = append(op.Reg.Outputs, regMask(r))
		}
		op.Reg.Clobbers = regMask(reg["clobbers"])
		op.Reg.ClobbersArg0 = boolean(reg, "clobbersArg0")
		op.Reg.ClobbersArg1 = boolean(reg, "clobbersArg1")
	}
	if _, ok := extra["hasAux"]; !ok {
		op.HasAux = op.AuxType != "" && op.AuxType != "invalid"
	}
	if _, ok := extra["hasAuxInt"]; !ok {
		op.HasAuxInt = op.AuxIntType != "" && op.AuxIntType != "invalid"
	}
	return op
}

func decodeBlock(m, extra map[string]any) *Block {
	return &Block{
		Name:       str(m, "name"),
		Controls:   int(integer(m, "controls")),
		Aux:        str(m, "aux"),
		AuxType:    str(extra, "auxType"),
		AuxIntType: str(extra, "auxIntType"),
		Raw:        m,
	}
}

func extraAt(l []map[string]any, i int) map[string]any {
	if i < len(l) {
		return l[i]
	}
	return nil
}

func anys[T any](x T) []any {
	switch x := any(x).(type) {
	case []any:
		return x
	case []map[string]any:
		r := make([]any, len(x))
		for i, m := range x {
			r[i] = m
		}
		return r
	}
	return nil
}

func asMap(x any) map[string]any {
	m, _ := x.(map[string]any)
	return m
}

func str(m map[string]any, k string) string {
	s, _ := m[k].(string)
	return s
}

func boolean(m map[string]any, k string) bool {
	b, _ := m[k].(bool)
	return b
}

func integer(m map[string]any, k string) int64 {
	n, _ := m[k].(json.Number)
	i, _ := strconv.ParseInt(string(n), 10, 64)
	return i
}

// regMask decodes a regMask, which is a struct {v1, v2 uint64} in recent
// trees and a uint64 in older ones.
func regMask(x any) RegMask {
	u := func(x any) uint64 {
		n, _ := x.(json.Number)
		v, _ := strconv.ParseUint(string(n), 10, 64)
		return v
	}
	switch x := x.(type) {
	case json.Number:
		return RegMask{Lo: u(x)}
	case map[string]any:
		return RegMask{Lo: u(x["v1"]), Hi: u(x["v2"])}
	}
	return RegMask{}
}
