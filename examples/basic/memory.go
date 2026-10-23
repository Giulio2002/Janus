package basic

import "sync/atomic"

// The functions below use sync/atomic and the runtime's memory routines.

// AtomicAdd adds d to *p atomically and returns the new value. atomic.AddUint64 is inlined:
// an LSE LDADDAL when internal/cpu.ARM64.HasATOMICS is set, an LDAXR/STLXR retry loop
// otherwise.
//
//go:noinline
func AtomicAdd(p *uint64, d uint64) uint64 { return atomic.AddUint64(p, d) }

// AtomicMax raises *p to at least v with an atomic load and a compare-and-swap retry loop,
// and returns the value *p had before.
//
//go:noinline
func AtomicMax(p *uint64, v uint64) uint64 {
	for {
		old := atomic.LoadUint64(p)
		if old >= v || atomic.CompareAndSwapUint64(p, old, v) {
			return old
		}
	}
}

// CopyBlock copies a 128-byte array with copy(), which the compiler lowers to a call of
// runtime.memmove.
//
//go:noinline
func CopyBlock(dst, src *[16]uint64) { copy(dst[:], src[:]) }

// ClearWords zeroes a slice with clear(), which the compiler lowers to a call of
// runtime.memclrNoHeapPointers.
//
//go:noinline
func ClearWords(b []uint64) { clear(b) }
