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

// holdCallee has a large frame, so a call to it grows the stack when it is small.
//
//go:noinline
func holdCallee(p *uint64, x uint64) uint64 {
	var buf [40]uint64
	buf[x%40] = *p
	*p = x
	return buf[x%40]
}

// HoldPtr keeps a pointer to its own stack frame (p = &a[i]) across a call that grows the
// stack. copystack adjusts the stored pointer, so *p is still a[i] after the growth.
//
//go:noinline
func HoldPtr(x uint64) uint64 {
	var a [2]uint64
	a[0] = x
	a[1] = x + 1
	p := &a[x&1]
	y := holdCallee(p, x+2)
	return *p + y + a[0]
}
