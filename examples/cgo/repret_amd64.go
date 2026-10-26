package cgo

// #include "cx87.h"
import "C"

// RepRetMax returns the unsigned maximum of a and b, computed by c_repret_umax: hand-written
// amd64 assembly (examples/cgo/cx87.c) that ends in `repz ret` (F3 C3), the idiom of perlasm
// code.
//
//go:noinline
func RepRetMax(a, b uint64) uint64 { return uint64(C.c_repret_umax(C.uint64_t(a), C.uint64_t(b))) }

var repRetSink uint64

// the example must be linked in (and so extractable) from any program that imports the package
func init() { repRetSink = RepRetMax(3, 5) }
