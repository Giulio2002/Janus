// Package stubdemo holds the example of the generic live-contract stubs
// (Janus/Contracts/LiveStub.lean): a function that allocates one object and stores a pointer
// into it, i.e. one runtime.newobject and one write barrier. It is built into a binary of its own
// (scripts/build/build-examples-rtmisc.sh), so that no other example's addresses change.
package stubdemo

// Node is a list node.
type Node struct {
	Next *Node
	V    uint64
}

// Cons returns a new node with Next = next and V = v: a heap allocation (runtime.newobject)
// and a pointer store into it (through the GC write barrier when the collector is marking).
//
//go:noinline
func Cons(next *Node, v uint64) *Node {
	return &Node{Next: next, V: v}
}
