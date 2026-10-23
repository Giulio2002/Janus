package basic

import "math/bits"

//go:noinline
func Add(x, y uint64) uint64 { return x + y }

//go:noinline
func Max(x, y uint64) uint64 {
	if x > y {
		return x
	}
	return y
}

//go:noinline
func Add128(xh, xl, yh, yl uint64) (uint64, uint64) {
	lo, c := bits.Add64(xl, yl, 0)
	hi, _ := bits.Add64(xh, yh, c)
	return hi, lo
}

//go:noinline
func Mul64(x, y uint64) (uint64, uint64) { return bits.Mul64(x, y) }

//go:noinline
func Sum(xs []uint64) uint64 {
	var s uint64
	for _, x := range xs {
		s += x
	}
	return s
}

//go:noinline
func Get(xs []uint64, i int) uint64 { return xs[i] }

//go:noinline
func Add256(z, x, y *[4]uint64) {
	var c uint64
	z[0], c = bits.Add64(x[0], y[0], 0)
	z[1], c = bits.Add64(x[1], y[1], c)
	z[2], c = bits.Add64(x[2], y[2], c)
	z[3], _ = bits.Add64(x[3], y[3], c)
}

//go:noinline
func Div(x, y uint64) uint64 { return x / y }

// AddThree calls Add twice, so its extraction contains a second function.
//
//go:noinline
func AddThree(x, y, z uint64) uint64 { return Add(Add(x, y), z) }

// The functions below load data. They exercise the extractor's read-only data copy
// (`Program.data`) and its reporting of writable globals.

// Table returns entry i&7 of a constant table. The array literal is a read-only static that
// the compiler places in .rodata and loads with ADRP+ADD and LDP.
//
//go:noinline
func Table(i uint64) uint64 {
	t := [8]uint64{0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
		0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917}
	return t[i&7]
}

// HexDigit indexes a string constant, which lives in .rodata.
//
//go:noinline
func HexDigit(i uint64) byte { return "0123456789abcdef"[i&15] }

// SetOne256 sets z to the 256-bit value 1: a 32-byte constant loaded from .rodata.
//
//go:noinline
func SetOne256(z *[4]uint64) { *z = [4]uint64{1, 0, 0, 0} }

// tbl is an initialised package-level variable. Go puts it in .noptrdata, which is
// writable, so the extractor reports the reference instead of copying the bytes.
var tbl = [8]uint64{0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
	0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917}

// GlobalTable returns tbl[i&7] (ADRP+ADD into .noptrdata).
//
//go:noinline
func GlobalTable(i uint64) uint64 { return tbl[i&7] }

var counter uint64

// Bump adds d to a zero-initialised global (in .noptrbss; ADRP+LDR, ADRP+STR).
//
//go:noinline
func Bump(d uint64) uint64 {
	counter += d
	return counter
}

// The functions below exercise loops over memory and calls (proof showcase).

// AddLimbs sets z = x + y modulo 2^256 with a carry loop over the four limbs.
//
//go:noinline
func AddLimbs(z, x, y *[4]uint64) {
	var c uint64
	for i := 0; i < 4; i++ {
		z[i], c = bits.Add64(x[i], y[i], c)
	}
}

// CopyWords copies min(len(dst), len(src)) words from src to dst and returns the count.
//
//go:noinline
func CopyWords(dst, src []uint64) int {
	n := len(src)
	if len(dst) < n {
		n = len(dst)
	}
	for i := 0; i < n; i++ {
		dst[i] = src[i]
	}
	return n
}

//go:noinline
func square(x uint64) uint64 { return x * x }

// SumSquares returns x*x + y*y (mod 2^64), calling the helper square twice.
//
//go:noinline
func SumSquares(x, y uint64) uint64 { return square(x) + square(y) }
