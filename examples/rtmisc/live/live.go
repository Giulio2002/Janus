// Package live holds the examples of the live allocation contracts (Janus/Contracts/Live.lean):
// functions that allocate several times, or a data-dependent number of times, and keep every
// object they allocated. It is built into a binary of its own
// (scripts/build-examples-rtmisc.sh), so that no other example's addresses change.
package live

// Cell is a heap object with a pointer field: a store into P goes through the GC write barrier
// when the collector is marking.
type Cell struct {
	P *uint64
	N uint64
}

// Three makes a slice A of n words and writes x into A[0], then allocates a Cell C and a slice B
// of n words, and stores &B[0] into C.P (through the write barrier when it is enabled).
//
//go:noinline
func Three(n int, x uint64) ([]uint64, []uint64, *Cell) {
	a := make([]uint64, n)
	a[0] = x
	c := new(Cell)
	b := make([]uint64, n)
	c.P = &b[0]
	return a, b, c
}

// Rows makes n rows of k zero words: an outer slice of n slice headers, and one makeslice per
// row, each stored into the outer slice (its pointer word through the write barrier).
//
//go:noinline
func Rows(n, k int) [][]uint64 {
	out := make([][]uint64, n)
	for i := range out {
		out[i] = make([]uint64, k)
	}
	return out
}

// Box is a heap object with one pointer field.
type Box struct {
	P *uint64
	N uint64
}

// Chain copies src into dst (memmove), allocates a slice t of n words (makeslice), copies src
// into t (memmove), and records n in bx.N and stores &t[0] into bx.P (through the GC write barrier when it is enabled):
// one runtime model threaded through memmove, makeslice, memmove and a barrier.
//
//go:noinline
func Chain(dst, src []uint64, bx *Box, n int) {
	copy(dst, src)
	t := make([]uint64, n)
	bx.N = uint64(n)
	copy(t, src)
	bx.P = &t[0]
}
