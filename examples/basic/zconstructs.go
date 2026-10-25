// This file is named to sort after the others (zalloc.go included), so that adding it left the
// addresses of the earlier example functions unchanged (some audit fixtures name them).

package basic

// The functions below exercise Go language constructs that need no runtime support beyond
// what the earlier examples already use (docs/COVERAGE.md, section 3, package M1): switches,
// labels and goto, generics, recursion, range over integers, arrays and function iterators,
// multiple and named results, struct and array values, non-escaping closures, method values
// and expressions, bit operations, variable shifts, division by constants, min/max, clear.
// Each has a theorem on arm64 (examples/proofs/<Name>.lean) and on amd64
// (examples/proofs-amd64/<Name>/Proof.lean).

// Triangle returns 0 + 1 + ... + n for n <= 8 and 0 for larger n. It is an expression switch
// whose cases fall through into each other; with 9 dense cases the compiler emits a jump table.
//
//go:noinline
func Triangle(n uint64) uint64 {
	var r uint64
	switch n {
	case 8:
		r += 8
		fallthrough
	case 7:
		r += 7
		fallthrough
	case 6:
		r += 6
		fallthrough
	case 5:
		r += 5
		fallthrough
	case 4:
		r += 4
		fallthrough
	case 3:
		r += 3
		fallthrough
	case 2:
		r += 2
		fallthrough
	case 1:
		r += 1
		fallthrough
	case 0:
		r += 0
	default:
		r = 0
	}
	return r
}

// GotoSum returns 1 + 2 + ... + n (mod 2^64), as a loop built from labels and goto.
//
//go:noinline
func GotoSum(n uint64) uint64 {
	var s, i uint64
loop:
	if i >= n {
		goto done
	}
	i++
	s += i
	goto loop
done:
	return s
}

// Find2D returns the row-major index 3*i + j of the first element of m equal to x, or 9 if
// there is none. The search leaves both loops with a labeled break.
//
//go:noinline
func Find2D(m *[3][3]uint64, x uint64) uint64 {
	r := uint64(9)
outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if m[i][j] == x {
				r = uint64(3*i + j)
				break outer
			}
		}
	}
	return r
}

// RowsWith returns the number of rows of m that contain x. A row is abandoned at its first
// match with a labeled continue.
//
//go:noinline
func RowsWith(m *[2][3]uint64, x uint64) uint64 {
	var n uint64
rows:
	for i := 0; i < 2; i++ {
		for j := 0; j < 3; j++ {
			if m[i][j] == x {
				n++
				continue rows
			}
		}
	}
	return n
}

// Log2 returns the floor of the base-2 logarithm of x, and 0 for x = 0 (a for loop with only
// a condition).
//
//go:noinline
func Log2(x uint64) uint64 {
	var n uint64
	for x > 1 {
		x >>= 1
		n++
	}
	return n
}

// Scaler is the constraint of the generic function total.
type Scaler interface{ Scale() uint64 }

// Meters and Feet have the same GC shape (uint64), so total is compiled once, for
// go.shape.uint64, and each instantiation passes its own dictionary, through which the shape
// code finds the Scale method.
type Meters uint64

// Scale converts to centimetres.
//
//go:noinline
func (m Meters) Scale() uint64 { return uint64(m) * 100 }

// Feet is a length in feet.
type Feet uint64

// Scale converts to centimetres, rounding a foot down to 30 cm.
//
//go:noinline
func (f Feet) Scale() uint64 { return uint64(f) * 30 }

//go:noinline
func total[T Scaler](a, b T) uint64 { return a.Scale() + b.Scale() }

// TotalMeters returns the length a + b in centimetres (the instantiation total[Meters]).
//
//go:noinline
func TotalMeters(a, b Meters) uint64 { return total(a, b) }

// TotalFeet returns the length a + b in centimetres (the instantiation total[Feet]).
//
//go:noinline
func TotalFeet(a, b Feet) uint64 { return total(a, b) }

// Fact returns n! (mod 2^64), recursively.
//
//go:noinline
func Fact(n uint64) uint64 {
	if n == 0 {
		return 1
	}
	return n * Fact(n-1)
}

// SumBelow returns 0 + 1 + ... + (n-1) (mod 2^64) for n > 0 and 0 for n <= 0, by range over
// an int.
//
//go:noinline
func SumBelow(n int) uint64 {
	var s uint64
	for i := range n {
		s += uint64(i)
	}
	return s
}

// ReverseArray stores the reverse of *in into *out. The array value a is a copy, so the result
// is right also when out and in are the same array.
//
//go:noinline
func ReverseArray(out, in *[4]uint64) {
	a := *in
	for i, x := range a {
		out[3-i] = x
	}
}

// DivMod10 returns the quotient and remainder of x by 10 as named results. The compiler
// replaces the divisions by a multiplication with a magic constant.
//
//go:noinline
func DivMod10(x uint64) (q, r uint64) {
	q = x / 10
	r = x % 10
	return
}

// Big is a struct of eight words.
type Big struct{ A, B, C, D, E, F, G, H uint64 }

// SwapBig exchanges *a and *b by value (struct assignment); a and b may be the same struct.
//
//go:noinline
func SwapBig(a, b *Big) { *a, *b = *b, *a }

//go:noinline
func twice(f func(uint64) uint64, x uint64) uint64 { return f(f(x)) }

// Compose returns f(f(x)) for f(v) = a*v + b (mod 2^64). The closure captures a and b; it does
// not escape, so it lives in Compose's frame.
//
//go:noinline
func Compose(a, b, x uint64) uint64 {
	return twice(func(v uint64) uint64 { return a*v + b }, x)
}

// Vec2 is a vector of two words.
type Vec2 struct{ X, Y uint64 }

// Dot returns the dot product of v and w (mod 2^64); a value receiver.
//
//go:noinline
func (v Vec2) Dot(w Vec2) uint64 { return v.X*w.X + v.Y*w.Y }

//go:noinline
func applyVec(f func(Vec2) uint64, w Vec2) uint64 { return f(w) }

//go:noinline
func applyVec2(f func(Vec2, Vec2) uint64, v, w Vec2) uint64 { return f(v, w) }

// DotBoth returns (a, b)·(c, d) + (a, b)·(d, c), the first through the method value
// Vec2{a, b}.Dot and the second through the method expression Vec2.Dot.
//
//go:noinline
func DotBoth(a, b, c, d uint64) uint64 {
	v := Vec2{a, b}
	return applyVec(v.Dot, Vec2{c, d}) + applyVec2(Vec2.Dot, v, Vec2{d, c})
}

// BitMerge returns, twice, the word whose bit i is bit i of y where m has a 1 and bit i of x
// where m has a 0: once as (x &^ m) | (y & m) and once as x ^ ((x ^ y) & m).
//
//go:noinline
func BitMerge(x, y, m uint64) (uint64, uint64) {
	return (x &^ m) | (y & m), x ^ ((x ^ y) & m)
}

// Shifts returns x << s, y >> s (arithmetic) and x >> s with Go's semantics for every s: a
// shift by 64 or more gives 0, or -1 for a negative y shifted right.
//
//go:noinline
func Shifts(x uint64, y int64, s uint64) (uint64, int64, uint64) {
	return x << s, y >> s, x >> s
}

// MinMax returns the smallest and largest of x, y, z and the distance between them.
//
//go:noinline
func MinMax(x, y, z int64) (lo, hi int64, spread uint64) {
	lo, hi = min(x, y, z), max(x, y, z)
	return lo, hi, uint64(hi) - uint64(lo)
}

// ClearArray sets every element of *p to zero.
//
//go:noinline
func ClearArray(p *[5]uint64) { clear(p[:]) }

// upTo is an iterator over 0, 1, ..., n-1.
func upTo(n int) func(func(int) bool) {
	return func(yield func(int) bool) {
		for i := 0; i < n; i++ {
			if !yield(i) {
				return
			}
		}
	}
}

// IterSum returns 0 + 1 + ... + (n-1) (mod 2^64) for n > 0 and 0 otherwise, by range over a
// function iterator that the compiler inlines.
//
//go:noinline
func IterSum(n int) uint64 {
	var s uint64
	for i := range upTo(n) {
		s += uint64(i)
	}
	return s
}

//go:noinline
func sumv(xs ...uint64) uint64 {
	var s uint64
	for _, x := range xs {
		s += x
	}
	return s
}

// Sum3 returns a + b + c (mod 2^64) through the variadic sumv; the argument slice lives in
// Sum3's frame.
//
//go:noinline
func Sum3(a, b, c uint64) uint64 { return sumv(a, b, c) }

// AlignUp rounds p up to a multiple of a, a power of two (uintptr arithmetic).
//
//go:noinline
func AlignUp(p, a uintptr) uintptr { return (p + a - 1) &^ (a - 1) }

// Slice3 returns xs[i:j:k]; it panics unless 0 <= i <= j <= k <= cap(xs).
//
//go:noinline
func Slice3(xs []uint64, i, j, k int) []uint64 { return xs[i:j:k] }

// Slice2 returns xs[i:j]; it panics unless 0 <= i <= j <= cap(xs).
//
//go:noinline
func Slice2(xs []uint64, i, j int) []uint64 { return xs[i:j] }

// Mod returns x % y; it panics (integer divide by zero) when y = 0.
//
//go:noinline
func Mod(x, y uint64) uint64 { return x % y }

// Counter is a struct with a pointer-receiver method.
type Counter struct{ N uint64 }

// Inc adds d to c.N and returns the new value.
//
//go:noinline
func (c *Counter) Inc(d uint64) uint64 {
	c.N += d
	return c.N
}

// IncTwice calls the pointer-receiver method Inc twice, statically, and returns the sum of the
// two results.
//
//go:noinline
func IncTwice(c *Counter, d uint64) uint64 { return c.Inc(d) + c.Inc(d) }

// MakeAdder returns the closure x ↦ x + a. The closure outlives the call, so it escapes: its
// funcval (the code address of MakeAdder.func1, then the captured a) is allocated on the heap
// with runtime.newobject.
//
//go:noinline
func MakeAdder(a uint64) func(uint64) uint64 {
	return func(x uint64) uint64 { return x + a }
}
