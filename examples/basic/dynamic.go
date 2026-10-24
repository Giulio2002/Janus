package basic

import "math/bits"

// The functions below make dynamic calls: through an interface, a method value, a closure, and
// an open-coded defer. A dynamic call's target is a register value, so a theorem about the
// caller states which code it reaches (docs/PROOFS.md, "Dynamic calls").

// Hasher is implemented by MulHasher and RotHasher.
type Hasher interface {
	Hash(x uint64) uint64
}

// MulHasher multiplies by K.
type MulHasher struct{ K uint64 }

//go:noinline
func (h *MulHasher) Hash(x uint64) uint64 { return x * h.K }

// RotHasher rotates left by 13 and adds K.
type RotHasher struct{ K uint64 }

//go:noinline
func (h *RotHasher) Hash(x uint64) uint64 { return bits.RotateLeft64(x, 13) + h.K }

// HashWith calls the Hash method of h's dynamic type, through h's itab.
//
//go:noinline
func HashWith(h Hasher, x uint64) uint64 { return h.Hash(x) }

// ApplyTwice calls the function value f twice: f(f(x)).
//
//go:noinline
func ApplyTwice(f func(uint64) uint64, x uint64) uint64 { return f(f(x)) }

// HashTwice hashes x twice through the method value h.Hash.
//
//go:noinline
func HashTwice(h *MulHasher, x uint64) uint64 { return ApplyTwice(h.Hash, x) }

// MapSum returns the sum of f(x) over xs (mod 2^64), calling f in a loop.
//
//go:noinline
func MapSum(f func(uint64) uint64, xs []uint64) uint64 {
	var s uint64
	for _, x := range xs {
		s += f(x)
	}
	return s
}

// AffineSum returns the sum of a*x + b over xs (mod 2^64), through a closure that captures a
// and b.
//
//go:noinline
func AffineSum(xs []uint64, a, b uint64) uint64 {
	return MapSum(func(x uint64) uint64 { return a*x + b }, xs)
}

// DeferAdd returns x + y: it returns x, and a deferred closure adds y to the named result
// (an open-coded defer).
//
//go:noinline
func DeferAdd(x, y uint64) (r uint64) {
	defer func() { r += y }()
	return x
}
