// Package sc is built with GOEXPERIMENT=sizespecializedmalloc (scripts/build-examples-rtmisc.sh,
// a binary of its own): an allocation whose size the compiler knows calls the size-specialised
// entry point of its size class (runtime/malloc_generated.go) instead of runtime.mallocgc.
package sc

// Pair is a 16-byte pointer-free object (size class 2).
type Pair struct{ A, B uint64 }

// NewPair allocates a Pair: runtime.newobject is replaced by
// runtime.mallocgcSmallNoScanSC2(16, type:Pair, true).
//
//go:noinline
func NewPair(a, b uint64) *Pair { return &Pair{a, b} }
