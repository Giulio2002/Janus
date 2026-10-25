// Package neon holds the Janus FFI example of an auto-vectorised C loop: a Go function that calls,
// through cgo, a C loop that gcc -O2 compiles to Advanced SIMD code on arm64. It is a package of
// its own so that the cgo wrapper names of example.com/cgo (which hash the package's files) stay
// the same.
package neon

// #include "cneon.h"
import "C"

import "unsafe"

// Count returns the number of bytes of b equal to c, computed by the C loop c_count.
//
//go:noinline
func Count(b []byte, c byte) uint64 {
	if len(b) == 0 {
		return 0
	}
	return uint64(C.c_count((*C.uint8_t)(unsafe.Pointer(&b[0])), C.uint64_t(len(b)), C.uint8_t(c)))
}
