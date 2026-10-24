// Package lib is an ordinary package. Its import path starts with "runtime.panic", so every
// symbol it defines starts with "runtime.panic" (runtime.panicky/lib.Zero). Round 6 F3.
package lib

//go:noinline
func Zero() uint64 { return 0 }
