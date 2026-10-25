// Package cgo holds the Janus FFI examples: Go functions that call C functions through cgo.
package cgo

// #include "cfuncs.h"
import "C"

import "unsafe"

// Add returns x + y, computed by the C function c_add.
//
//go:noinline
func Add(x, y uint64) uint64 { return uint64(C.c_add(C.uint64_t(x), C.uint64_t(y))) }

// Sum returns the sum of xs, computed by the C loop c_sum.
//
//go:noinline
func Sum(xs []uint64) uint64 {
	if len(xs) == 0 {
		return 0
	}
	return uint64(C.c_sum((*C.uint64_t)(unsafe.Pointer(&xs[0])), C.uint64_t(len(xs))))
}

// Store writes v to *p through the C function c_store.
//
//go:noinline
func Store(p *uint64, v uint64) { C.c_store((*C.uint64_t)(unsafe.Pointer(p)), C.uint64_t(v)) }

// Count returns the number of bytes of b equal to c, computed by the C loop c_count, which gcc
// -O2 auto-vectorises.
//
//go:noinline
func Count(b []byte, c byte) uint64 {
	if len(b) == 0 {
		return 0
	}
	return uint64(C.c_count((*C.uint8_t)(unsafe.Pointer(&b[0])), C.uint64_t(len(b)), C.uint8_t(c)))
}
