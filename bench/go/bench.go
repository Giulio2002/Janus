// Package bench holds self-written Go functions that stress the Janus proof automation:
// a long straight-line function, nested loops, a deep call chain, many possibly aliasing
// pointers and a large stack frame. Every function is proved on arm64 and amd64
// (bench/proofs-arm64, bench/proofs-amd64); scripts/bench.sh times the proofs.
//
// This module is separate from examples/basic so that adding or changing a benchmark never
// moves an address the example proofs mention.
package bench

import "math/bits"

// MulAdd8 computes z + x*y + c over 8 little-endian 64-bit limbs: it stores the low 512 bits
// in z and returns the carry limb. Fully unrolled, straight-line code.
//
//go:noinline
func MulAdd8(z, x *[8]uint64, y, c uint64) uint64 {
	var hi, lo, cc uint64
	hi, lo = bits.Mul64(x[0], y)
	lo, cc = bits.Add64(lo, z[0], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[0], c = lo, hi+cc
	hi, lo = bits.Mul64(x[1], y)
	lo, cc = bits.Add64(lo, z[1], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[1], c = lo, hi+cc
	hi, lo = bits.Mul64(x[2], y)
	lo, cc = bits.Add64(lo, z[2], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[2], c = lo, hi+cc
	hi, lo = bits.Mul64(x[3], y)
	lo, cc = bits.Add64(lo, z[3], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[3], c = lo, hi+cc
	hi, lo = bits.Mul64(x[4], y)
	lo, cc = bits.Add64(lo, z[4], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[4], c = lo, hi+cc
	hi, lo = bits.Mul64(x[5], y)
	lo, cc = bits.Add64(lo, z[5], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[5], c = lo, hi+cc
	hi, lo = bits.Mul64(x[6], y)
	lo, cc = bits.Add64(lo, z[6], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[6], c = lo, hi+cc
	hi, lo = bits.Mul64(x[7], y)
	lo, cc = bits.Add64(lo, z[7], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z[7], c = lo, hi+cc
	return c
}

// MulAdd8x3 performs three 8-limb multiply-adds, z_k + x*y_k for k < 3 (the rows of a
// schoolbook multiplication), storing the low 512 bits in z_k and returning the carry limbs.
// About 300 instructions of straight-line code.
//
//go:noinline
func MulAdd8x3(z0, z1, z2, x *[8]uint64, y0, y1, y2 uint64) (c0, c1, c2 uint64) {
	var hi, lo, cc, c uint64
	// row 0: z0 + x*y0
	c = 0
	hi, lo = bits.Mul64(x[0], y0)
	lo, cc = bits.Add64(lo, z0[0], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[0], c = lo, hi+cc
	hi, lo = bits.Mul64(x[1], y0)
	lo, cc = bits.Add64(lo, z0[1], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[1], c = lo, hi+cc
	hi, lo = bits.Mul64(x[2], y0)
	lo, cc = bits.Add64(lo, z0[2], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[2], c = lo, hi+cc
	hi, lo = bits.Mul64(x[3], y0)
	lo, cc = bits.Add64(lo, z0[3], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[3], c = lo, hi+cc
	hi, lo = bits.Mul64(x[4], y0)
	lo, cc = bits.Add64(lo, z0[4], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[4], c = lo, hi+cc
	hi, lo = bits.Mul64(x[5], y0)
	lo, cc = bits.Add64(lo, z0[5], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[5], c = lo, hi+cc
	hi, lo = bits.Mul64(x[6], y0)
	lo, cc = bits.Add64(lo, z0[6], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[6], c = lo, hi+cc
	hi, lo = bits.Mul64(x[7], y0)
	lo, cc = bits.Add64(lo, z0[7], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z0[7], c = lo, hi+cc
	c0 = c
	// row 1: z1 + x*y1
	c = 0
	hi, lo = bits.Mul64(x[0], y1)
	lo, cc = bits.Add64(lo, z1[0], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[0], c = lo, hi+cc
	hi, lo = bits.Mul64(x[1], y1)
	lo, cc = bits.Add64(lo, z1[1], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[1], c = lo, hi+cc
	hi, lo = bits.Mul64(x[2], y1)
	lo, cc = bits.Add64(lo, z1[2], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[2], c = lo, hi+cc
	hi, lo = bits.Mul64(x[3], y1)
	lo, cc = bits.Add64(lo, z1[3], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[3], c = lo, hi+cc
	hi, lo = bits.Mul64(x[4], y1)
	lo, cc = bits.Add64(lo, z1[4], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[4], c = lo, hi+cc
	hi, lo = bits.Mul64(x[5], y1)
	lo, cc = bits.Add64(lo, z1[5], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[5], c = lo, hi+cc
	hi, lo = bits.Mul64(x[6], y1)
	lo, cc = bits.Add64(lo, z1[6], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[6], c = lo, hi+cc
	hi, lo = bits.Mul64(x[7], y1)
	lo, cc = bits.Add64(lo, z1[7], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z1[7], c = lo, hi+cc
	c1 = c
	// row 2: z2 + x*y2
	c = 0
	hi, lo = bits.Mul64(x[0], y2)
	lo, cc = bits.Add64(lo, z2[0], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[0], c = lo, hi+cc
	hi, lo = bits.Mul64(x[1], y2)
	lo, cc = bits.Add64(lo, z2[1], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[1], c = lo, hi+cc
	hi, lo = bits.Mul64(x[2], y2)
	lo, cc = bits.Add64(lo, z2[2], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[2], c = lo, hi+cc
	hi, lo = bits.Mul64(x[3], y2)
	lo, cc = bits.Add64(lo, z2[3], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[3], c = lo, hi+cc
	hi, lo = bits.Mul64(x[4], y2)
	lo, cc = bits.Add64(lo, z2[4], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[4], c = lo, hi+cc
	hi, lo = bits.Mul64(x[5], y2)
	lo, cc = bits.Add64(lo, z2[5], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[5], c = lo, hi+cc
	hi, lo = bits.Mul64(x[6], y2)
	lo, cc = bits.Add64(lo, z2[6], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[6], c = lo, hi+cc
	hi, lo = bits.Mul64(x[7], y2)
	lo, cc = bits.Add64(lo, z2[7], 0)
	hi += cc
	lo, cc = bits.Add64(lo, c, 0)
	z2[7], c = lo, hi+cc
	c2 = c
	return
}

// Nested is a doubly nested loop: the sum of i*m + j over i < n, j < m (mod 2^64).
//
//go:noinline
func Nested(n, m uint64) uint64 {
	var s uint64
	for i := uint64(0); i < n; i++ {
		for j := uint64(0); j < m; j++ {
			s += i*m + j
		}
	}
	return s
}

// A call chain five levels deep: Chain1 calls Chain2 calls ... Chain5.

//go:noinline
func Chain5(x uint64) uint64 { return x*3 + 1 }

//go:noinline
func Chain4(x uint64) uint64 { return Chain5(x) + 4 }

//go:noinline
func Chain3(x uint64) uint64 { return Chain4(x) ^ 3 }

//go:noinline
func Chain2(x uint64) uint64 { return Chain3(x+2) + x }

//go:noinline
func Chain1(x uint64) uint64 { return Chain2(x) + 1 }

// Alias4 updates four words through pointers that may alias each other in any way.
//
//go:noinline
func Alias4(a, b, c, d *uint64) {
	*a += *b
	*c ^= *d
	*b += *c
	*d = *a + 1
}

// BigFrame fills a 64-word local array (a 512-byte stack frame) and reads one entry back at
// a variable index.
//
//go:noinline
func BigFrame(x, k uint64) uint64 {
	var buf [64]uint64
	for i := range buf {
		buf[i] = x + uint64(i)
	}
	return buf[k&63]
}
