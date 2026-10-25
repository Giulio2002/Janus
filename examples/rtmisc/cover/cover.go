// Package cover is built with -cover -covermode=count (scripts/build-examples-rtmisc.sh): every
// basic block increments its counter in the package's coverage counter array.
package cover

// Clamp returns min(x, hi).
//
//go:noinline
func Clamp(x, hi uint64) uint64 {
	if x > hi {
		return hi
	}
	return x
}
