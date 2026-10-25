// Package avx holds the Janus FFI example whose C code is compiled by clang at -O3
// -march=x86-64-v3 (built with CC=clang, see scripts/build-examples-cgo.sh): a loop that clang
// vectorises with AVX2 on YMM registers.
package avx

// #cgo CFLAGS: -O3 -march=x86-64-v3
// #include "cavx.h"
import "C"

import "unsafe"

// Dot32 returns a[0]·b[0] + … + a[n-1]·b[n-1] modulo 2^32, n = len(a), computed by the C loop
// c_dot32 (AVX2 VPMULLD/VPADDD); 0 if a is empty or b is shorter than a.
//
//go:noinline
func Dot32(a, b []uint32) uint32 {
	if len(a) == 0 || len(b) < len(a) {
		return 0
	}
	return uint32(C.c_dot32((*C.uint32_t)(unsafe.Pointer(&a[0])), (*C.uint32_t)(unsafe.Pointer(&b[0])), C.uint64_t(len(a))))
}
