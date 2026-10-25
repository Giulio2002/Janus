// Package cabi holds the Janus C ABI examples (docs/FFI.md, section 5): Go functions that call,
// through cgo, C functions with stack arguments, floating-point arguments and results, a
// homogeneous floating-point struct by value, a 32-byte struct result (indirect: X8 / the hidden
// RDI pointer) and a variadic callee.
package cabi

// #include "kabi.h"
import "C"

// Stack10 returns a + 2b + 3c + 4d + 5e + 6f + 7g + 8h + 9i + 10j, computed by k_stack10, whose
// last arguments are passed on the stack.
//
//go:noinline
func Stack10(a, b, c, d, e, f, g, h int64, i int32, j int64) int64 {
	return int64(C.k_stack10(C.int64_t(a), C.int64_t(b), C.int64_t(c), C.int64_t(d), C.int64_t(e),
		C.int64_t(f), C.int64_t(g), C.int64_t(h), C.int32_t(i), C.int64_t(j)))
}

// FP returns (a - b) * c, computed by k_fp in floating-point registers.
//
//go:noinline
func FP(a float64, b float32, c float64) float64 {
	return float64(C.k_fp(C.double(a), C.float(b), C.double(c)))
}

// PMix returns ((ax + bx) * (ay - by), n + 1), computed by k_pmix from two structs passed by value;
// the result is a struct too.
//
//go:noinline
func PMix(ax, ay, bx, by float64, n int64) (float64, int64) {
	r := C.k_pmix(C.struct_k_pt{x: C.double(ax), y: C.double(ay)},
		C.struct_k_pt{x: C.double(bx), y: C.double(by)}, C.int64_t(n))
	return float64(r.s), int64(r.n)
}

// Big returns the four words of the 32-byte struct k_big(x, y) returns: x + y, x - y, x * y and
// x ^ y.
//
//go:noinline
func Big(x, y int64) (int64, int64, int64, int64) {
	r := C.k_big(C.int64_t(x), C.int64_t(y))
	return int64(r.a), int64(r.b), int64(r.c), int64(r.d)
}

// VSum8 returns a + b + ... + h, computed by the variadic k_vsum(8, a, ..., h) (cgo cannot call
// a variadic function, so the C function k_vsum8 makes the call).
//
//go:noinline
func VSum8(a, b, c, d, e, f, g, h int64) int64 {
	return int64(C.k_vsum8(C.int64_t(a), C.int64_t(b), C.int64_t(c), C.int64_t(d), C.int64_t(e),
		C.int64_t(f), C.int64_t(g), C.int64_t(h)))
}
