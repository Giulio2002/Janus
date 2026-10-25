// This file is named to sort after the others, so that adding it left the addresses of the
// earlier example functions unchanged (some audit fixtures name them).

package basic

// The functions below use the runtime's string and slice helpers. Their proofs treat those
// helpers as contracts (Janus/Contracts/String.lean, Janus/Contracts/Slice.lean and their
// amd64 counterparts): `janus extract --contract` leaves them out and each theorem states, as a
// hypothesis, what it assumes they do.

// Concat returns a + b (runtime.concatstring2).
//
//go:noinline
func Concat(a, b string) string { return a + b }

// ToBytes returns a new byte slice holding the bytes of s (runtime.stringtoslicebyte).
//
//go:noinline
func ToBytes(s string) []byte { return []byte(s) }

// FromBytes returns the string holding the bytes of b (runtime.slicebytetostring).
//
//go:noinline
func FromBytes(b []byte) string { return string(b) }

// SumRunes returns the sum of the code points of s, decoded as UTF-8 by for-range: an ASCII
// byte inline, anything else by runtime.decoderune (invalid sequences give U+FFFD).
//
//go:noinline
func SumRunes(s string) (sum uint64) {
	for _, r := range s {
		sum += uint64(r)
	}
	return
}

// RuneLen returns the number of runes of s (runtime.countrunes).
//
//go:noinline
func RuneLen(s string) int { return len([]rune(s)) }

// Point is a 24-byte struct without pointers.
type Point struct{ X, Y, Z int64 }

// AppendPoint appends p to s (runtime.growslice with a 24-byte element type when s is full).
//
//go:noinline
func AppendPoint(s []Point, p Point) []Point { return append(s, p) }

// CopyNodes copies src into dst, a slice of pointers (runtime.typedslicecopy), and returns the
// number of elements copied.
//
//go:noinline
func CopyNodes(dst, src []*Node) int { return copy(dst, src) }
