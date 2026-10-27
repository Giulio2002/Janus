package softcheck

import (
	"os"
	"strconv"
	"testing"
)

func cases() int {
	if s := os.Getenv("SOFTCHECK_N"); s != "" {
		if n, err := strconv.Atoi(s); err == nil {
			return n
		}
	}
	return 400000
}

// TestAgainstIEEE: whenever the exact result is not tiny (zero, or at least 2^-1022 in
// magnitude), or an operand is zero, infinite or NaN, the runtime's result is the IEEE one
// (NaN for NaN); these are the preconditions of the Lean contracts.
func TestAgainstIEEE(t *testing.T) {
	for _, op := range []byte{'+', '-', '*', '/'} {
		r := Run(op, cases(), 1)
		t.Logf("%c: %d cases, %d covered by the contract and agree, %d tiny (%d differ from IEEE)",
			op, r.Cases, r.Checked, r.Tiny, r.TinyMismatch)
		for _, b := range r.Bad {
			t.Errorf("%c: %s", op, b)
		}
		if r.Checked == 0 {
			t.Errorf("%c: nothing checked", op)
		}
	}
}

// TestSubnormalResultsDiffer documents the known deviation: the runtime's addition (and so
// subtraction) does not give the IEEE result for many subnormal results (a cancellation that
// leaves a subnormal gets the wrong magnitude), so the contracts do not claim it. If this test
// ever fails (the runtime was fixed) the preconditions can be dropped. Multiplication and
// division showed no deviation on the draws of this test, but the contracts keep the same
// precondition: nothing here proves they have none.
func TestSubnormalResultsDiffer(t *testing.T) {
	for _, op := range []byte{'+', '*', '/'} {
		r := Run(op, cases(), 2)
		t.Logf("%c: %d tiny cases, %d differ from IEEE", op, r.Tiny, r.TinyMismatch)
		if op == '+' && r.TinyMismatch == 0 {
			t.Errorf("%c: no subnormal-result deviation observed", op)
		}
	}
}

// Fixed vectors: Go 1.26's runtime gives these subnormal results, IEEE gives the others.
func TestKnownDeviations(t *testing.T) {
	for _, c := range []struct{ f, g, ieee, runtime uint64 }{
		{0x0170000000155555, 0x816fffffffffffff, 0x0000055555600000, 0x00000000002aaaab},
		{0x81a0000003ffffff, 0x01a0000004000000, 0x0000000002000000, 0x0000000000000002},
		{0x80d0000000000014, 0x00d0000000000003, 0x8000000000011000, 0x8000000000000022},
	} {
		if got := IEEE('+', c.f, c.g); got != c.ieee {
			t.Errorf("hardware %#x + %#x = %#x, want %#x", c.f, c.g, got, c.ieee)
		}
		if got := fadd64(c.f, c.g); got != c.runtime {
			t.Errorf("runtime.fadd64(%#x, %#x) = %#x, want %#x", c.f, c.g, got, c.runtime)
		}
		if !ExactTiny('+', c.f, c.g) {
			t.Errorf("%#x + %#x should have a tiny exact result", c.f, c.g)
		}
	}
}
