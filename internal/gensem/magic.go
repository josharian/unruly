package gensem

// Copied from cmd/compile/internal/ssa/magic.go, returning the data
// structs' fields as maps. See GOLICENSE in package rules.

import (
	"math/big"
	"math/bits"
)

func umagic(n uint, c int64) map[string]uint64 {
	d := uint64(c) << (64 - n) >> (64 - n)
	C := new(big.Int).SetUint64(d)
	s := C.BitLen()
	M := big.NewInt(1)
	M.Lsh(M, n+uint(s))
	M.Add(M, C)
	M.Sub(M, big.NewInt(1))
	M.Div(M, C)
	if M.Bit(int(n)) != 1 {
		panic("n+1st bit isn't set")
	}
	M.SetBit(M, int(n), 0)
	return map[string]uint64{"S": uint64(s), "M": M.Uint64()}
}

func smagicOK(n uint, c int64) bool {
	if c < 0 {
		return false
	}
	return c&(c-1) != 0
}

func smagic(n uint, c int64) map[string]uint64 {
	C := new(big.Int).SetInt64(c)
	s := C.BitLen() - 1
	M := big.NewInt(1)
	M.Lsh(M, n+uint(s))
	M.Add(M, C)
	M.Sub(M, big.NewInt(1))
	M.Div(M, C)
	if M.Bit(int(n)) != 0 {
		panic("n+1st bit is set")
	}
	if M.Bit(int(n-1)) == 0 {
		panic("nth bit is not set")
	}
	return map[string]uint64{"S": uint64(s), "M": M.Uint64()}
}

func udivisibleOK(n uint, c int64) bool {
	d := uint64(c) << (64 - n) >> (64 - n)
	return d&(d-1) != 0
}

func inverse(d0, mask uint64) uint64 {
	m := d0
	for range 5 {
		m = m * (2 - m*d0)
	}
	return m & mask
}

func udivisible(n uint, c int64) map[string]uint64 {
	d := uint64(c) << (64 - n) >> (64 - n)
	k := bits.TrailingZeros64(d)
	d0 := d >> uint(k)
	mask := ^uint64(0) >> (64 - n)
	return map[string]uint64{"K": uint64(k), "M": inverse(d0, mask), "Max": mask / d}
}

func sdivisible(n uint, c int64) map[string]uint64 {
	d := uint64(c)
	k := bits.TrailingZeros64(d)
	d0 := d >> uint(k)
	mask := ^uint64(0) >> (64 - n)
	a := ((mask >> 1) / d0) & -(1 << uint(k))
	return map[string]uint64{"K": uint64(k), "M": inverse(d0, mask), "A": a, "Max": (2 * a) >> uint(k)}
}
