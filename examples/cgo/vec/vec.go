// Package vec holds the Janus FFI example whose C code is compiled by clang (built with
// CC=clang, see scripts/build-examples-cgo.sh): a loop that clang -O2 vectorises with SSE2.
package vec

// #include "cvec.h"
import "C"

import "unsafe"

// Sum32 returns the sum of xs modulo 2^32, computed by the C loop c_sum32 (SSE2 PADDD).
//
//go:noinline
func Sum32(xs []int32) int32 {
	if len(xs) == 0 {
		return 0
	}
	return int32(C.c_sum32((*C.int32_t)(unsafe.Pointer(&xs[0])), C.uint64_t(len(xs))))
}
