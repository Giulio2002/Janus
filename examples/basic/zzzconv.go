// This file is named to sort after zzerrf.go, so that adding it left the addresses of the
// earlier example functions unchanged (some audit fixtures name them).

package basic

// boxNode is a pointer-free node: its allocation is runtime.newobject of 16 bytes, no scan.
type boxNode struct{ A, B uint64 }

// BoxAfterNew allocates a node (a live allocating call: runtime.newobject), then boxes a string and a number
// in interfaces: runtime.convTstring after that live call, and runtime.convT64 after both.
// Its proofs treat the three runtime functions as live contracts (Janus/Contracts/Live.lean, IfaceLive.lean).
//
//go:noinline
func BoxAfterNew(s string, v uint64) (*boxNode, any, any) {
	return &boxNode{v, v + 1}, s, v
}
