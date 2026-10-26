package basic

// Mutual recursion (Janus.Tactic.Summary.induction_mutual) and writable globals
// (Janus.Spec.GlobalsInit): examples/proofs/{IsEven,CycA,MulAlgo}.lean and their amd64 proofs.

// IsEven reports whether n is even, by mutual recursion with IsOdd.
//
//go:noinline
func IsEven(n uint64) bool {
	if n == 0 {
		return true
	}
	return IsOdd(n - 1)
}

// IsOdd reports whether n is odd, by mutual recursion with IsEven.
//
//go:noinline
func IsOdd(n uint64) bool {
	if n == 0 {
		return false
	}
	return IsEven(n - 1)
}

// CycA, CycB and CycC form a 3-cycle of calls (A(n) -> B(n) -> C(n, t, u) -> A(n-1)) with three
// different frames: CycA keeps nothing across its call, CycB spills three outgoing arguments,
// CycC keeps a four-word array in its frame.
//
//go:noinline
func CycA(n uint64) uint64 {
	if n == 0 {
		return 1
	}
	return CycB(n) + 1
}

//go:noinline
func CycB(n uint64) uint64 {
	t := n ^ 0x5a
	return CycC(n, t, n+t) ^ t
}

//go:noinline
func CycC(n, k, j uint64) uint64 {
	var w [4]uint64
	w[0], w[1], w[2], w[3] = n, k, j, k^j
	r := CycA(n - 1)
	return r + w[0] + w[1]*w[2] + w[3]
}

// karatsubaCut mirrors math/big's karatsubaThreshold: an initialised package variable, so Go
// places it in .noptrdata (writable). mulBias is zero-initialised (.noptrbss).
var karatsubaCut = 40

var mulBias int

// MulAlgo picks an algorithm the way nat.mul does: 1 (schoolbook) below the threshold, 2
// (Karatsuba) at or above it, offset by mulBias.
//
//go:noinline
func MulAlgo(n int) int {
	if n < karatsubaCut {
		return 1 + mulBias
	}
	return 2 + mulBias
}
