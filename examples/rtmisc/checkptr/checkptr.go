// Package checkptr is built with -gcflags=example.com/rtmisc/checkptr=-d=checkptr
// (scripts/build-examples-rtmisc.sh): every conversion of an unsafe.Pointer to a pointer type
// calls runtime.checkptrAlignment.
package checkptr

import "unsafe"

// Word reads the uint64 at p through a converted unsafe.Pointer.
//
//go:noinline
func Word(p unsafe.Pointer) uint64 { return *(*uint64)(p) }
