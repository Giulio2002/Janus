// Package cenv holds the Janus C environment examples (docs/FFI.md, sections 2-4): C functions
// that use writable globals, thread-local storage, function pointers, libc through the PLT,
// setjmp/longjmp, alloca and atomics, and a C function that calls back into Go (//export).
package cenv

// #include <stdlib.h>
// #include "cenv.h"
import "C"

import "unsafe"

// GoTwice returns 2x. C calls it (e_callgo) through cgo's export wrapper.
//
//export GoTwice
func GoTwice(x C.int64_t) C.int64_t { return 2 * x }

// Bump adds x * e_scale to the C global e_counter and returns it.
func Bump(x int64) int64 { return int64(C.e_bump(C.int64_t(x))) }

// TLSAdd adds x to the C thread-locals e_tls and e_tls_ie and returns both.
func TLSAdd(x int64) (int64, int64) {
	return int64(C.e_tls_add(C.int64_t(x))), int64(C.e_tls_ie_add(C.int64_t(x)))
}

// ArgMin returns the index of the first minimum of xs, found by e_argmin with a comparator.
func ArgMin(xs []int64) int {
	if len(xs) == 0 {
		return 0
	}
	return int(C.e_argmin_i64((*C.int64_t)(unsafe.Pointer(&xs[0])), C.size_t(len(xs))))
}

// Libc copies s through e_libc (via a heap duplicate) and returns the copy and the length it
// reports.
func Libc(s string) (string, int64) {
	cs := C.CString(s)
	defer C.free(unsafe.Pointer(cs))
	d := (*C.char)(C.malloc(C.size_t(len(s) + 1)))
	defer C.free(unsafe.Pointer(d))
	n := int64(C.e_libc(cs, d))
	return C.GoString(d), n
}

// SetJmp returns e_setjmp(v): 1 if v != 0 (through longjmp), 0 otherwise.
func SetJmp(v int32) int32 { return int32(C.e_setjmp(C.int(v))) }

// Alloca returns 0 + 1 + ... + (n - 1), computed through an alloca'd array.
func Alloca(n uint64) int64 { return int64(C.e_alloca(C.size_t(n))) }

// AtomicInc atomically increments *p in C and returns the new value.
func AtomicInc(p *uint32) uint32 { return uint32(C.e_atomic_inc((*C.uint32_t)(unsafe.Pointer(p)))) }

// CallGo returns e_callgo(x) = GoTwice(x) + 1: Go calls C, which calls back into Go.
func CallGo(x int64) int64 { return int64(C.e_callgo(C.int64_t(x))) }
