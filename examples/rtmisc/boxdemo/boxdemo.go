// Package boxdemo holds the example of the live boxing contracts (Janus/Contracts/IfaceLive.lean): a function that
// makes a live allocating call (runtime.newobject) and then boxes a string and a number in interfaces
// (runtime.convTstring after the live call, runtime.convT64 after both). It is built into a binary of its own
// (scripts/build-examples-rtmisc.sh), so that no other example's addresses change.
package boxdemo

// Node is a pointer-free two-word node.
type Node struct{ A, B uint64 }

// BoxAfterNew allocates a node, then boxes s and v in interfaces.
//
//go:noinline
func BoxAfterNew(s string, v uint64) (*Node, any, any) {
	return &Node{v, v + 1}, s, v
}
