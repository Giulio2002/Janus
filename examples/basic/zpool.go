// This file is named to sort after the others, so that adding it left the addresses of the
// earlier example functions unchanged (some audit fixtures name them).

package basic

import (
	"slices"
	"sync"
)

// The function below uses a sync.Pool-backed scratch buffer, the pattern of math/big's
// temporary stack (getStack / stack.free: a Get with a type assertion, new on a miss, a Put
// when done). Its proofs treat sync.(*Pool).Get and sync.(*Pool).Put as contracts
// (Janus/Contracts/Pool.lean, PoolAmd64.lean), so the pool's concurrency internals
// (runtime_procPin, poolDequeue, the allPools mutex) are not extracted, and the allocation of
// a new buffer as the newobject contract (Janus/Contracts/Alloc.lean).

// scratch is a pointer-free scratch buffer of four words.
type scratch struct{ w [4]uint64 }

// scratchPool holds scratch buffers between calls; its New is nil, as for math/big's
// stackPool.
var scratchPool sync.Pool

// ScratchSum stores a and b into a pooled scratch buffer (a new one when the pool has none),
// gives the buffer back to the pool and returns a ^ b.
//
//go:noinline
func ScratchSum(a, b uint64) uint64 {
	s, _ := scratchPool.Get().(*scratch)
	if s == nil {
		s = new(scratch)
	}
	s.w[0] = a
	s.w[1] = b
	r := s.w[0] ^ s.w[1]
	scratchPool.Put(s)
	return r
}

// stack is a pooled scratch stack of words, as math/big's: a 24-byte header holding a slice.
type stack struct{ w []uint64 }

// stackPool holds stacks between calls; its New is nil.
var stackPool sync.Pool

// StackGrow takes a stack from the pool (a new one when the pool has none), gives it back
// with a deferred Put, and grows its backing array to room for n words (slices.Grow:
// runtime.growslice and memclrNoHeapPointers, and the GC write barrier when it stores the new
// array into the pooled header). It returns the capacity it got. This is math/big's pattern:
// getStack, a deferred stk.free, and the stack's growth.
//
//go:noinline
func StackGrow(n int) int {
	s, _ := stackPool.Get().(*stack)
	if s == nil {
		s = new(stack)
	}
	defer stackPool.Put(s)
	s.w = slices.Grow(s.w[:0], n)
	return cap(s.w)
}
