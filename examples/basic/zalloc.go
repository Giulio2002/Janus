// This file is named to sort after the others, so that adding it left the addresses of the
// earlier example functions unchanged (some audit fixtures name them).

package basic

// The functions below allocate on the heap. Their proofs treat the runtime's allocator
// (runtime.mallocgc and its wrappers newobject, makeslice, growslice) and the GC write
// barrier as contracts: `janus extract --contract` leaves those functions out, and each
// theorem states, as a hypothesis, what it assumes they do (Janus/Contracts/Alloc.lean).

// Pair is a two-word heap object without pointers.
type Pair struct{ A, B uint64 }

// NewPair returns a new heap-allocated Pair holding a and b (runtime.newobject).
//
//go:noinline
func NewPair(a, b uint64) *Pair { return &Pair{a, b} }

// MakeSlice returns a new zeroed slice of n words (runtime.makeslice).
//
//go:noinline
func MakeSlice(n int) []uint64 { return make([]uint64, n) }

// AppendOne appends x to s, growing the backing array through runtime.growslice when s is
// full.
//
//go:noinline
func AppendOne(s []uint64, x uint64) []uint64 { return append(s, x) }

// Node is a heap object with a pointer field.
type Node struct {
	Next *Node
	Val  uint64
}

// SetNext stores q into n.Next. Storing a pointer into a heap object goes through the GC
// write barrier when it is enabled (runtime.writeBarrier, runtime.gcWriteBarrier2).
//
//go:noinline
func SetNext(n, q *Node) { n.Next = q }
