package cgo

// #include "cx87.h"
import "C"

import "unsafe"

// MulLD stores in r the x87 long double product of a and b, computed by the C function
// c_ldmul (which calls ld_mul). Each operand is a C long double: 16 bytes, the
// double-extended value in the low 10.
//
//go:noinline
func MulLD(a, b, r *[16]byte) {
	C.c_ldmul((*C.ld16)(unsafe.Pointer(a)), (*C.ld16)(unsafe.Pointer(b)), (*C.ld16)(unsafe.Pointer(r)))
}

// Switch returns c_switch(k, x), a C switch compiled to a jump table.
//
//go:noinline
func Switch(k, x uint64) uint64 { return uint64(C.c_switch(C.uint64_t(k), C.uint64_t(x))) }
