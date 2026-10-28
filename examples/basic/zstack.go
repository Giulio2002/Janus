package basic

// Stack-growth (R7) examples: functions whose prologue calls runtime.morestack on a small
// stack. See examples/proofs/*.lean and docs/COVERAGE.md row 20.

// BigLocal has a 176-byte frame (> abi.StackSmall = 128), so its prologue always calls
// morestack when the goroutine stack is small. It writes buf[i&15] = x and returns buf[0], so
// the result is x when i&15 = 0 and 0 otherwise.
//
//go:noinline
func BigLocal(x, i uint64) uint64 {
	var buf [20]uint64
	buf[i&15] = x
	return buf[0]
}

// SumRec sums 0 + 1 + ... + n recursively; proved WITHOUT assuming the whole stack fits (it
// grows as the recursion deepens).
//
//go:noinline
func SumRec(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return n + SumRec(n-1)
}

// holdCallee has a 176-byte frame, so a call to it grows a small stack. It stores buf[0] through
// p: x when x&15 = 0, else 0.
//
//go:noinline
func holdCallee(p *uint64, x uint64) {
	var buf [20]uint64
	buf[x&15] = x
	*p = buf[0]
}

// pick returns p when x is even, else q.
//
//go:noinline
func pick(p, q *uint64, x uint64) *uint64 {
	if x&1 == 0 {
		return p
	}
	return q
}

// HoldPtr keeps p, a pointer into its own frame (&a[x&1], returned by pick), in its frame
// across a call that grows the stack. copystack adjusts p (a pointer slot of HoldPtr's frame)
// and the callee's pointer argument, so the callee's store and the reads after the call reach
// the moved array.
//
//go:noinline
func HoldPtr(x uint64) uint64 {
	var a [2]uint64
	a[0] = x
	a[1] = x + 1
	p := pick(&a[0], &a[1], x)
	holdCallee(p, x)
	return *p + a[0] + a[1]
}
