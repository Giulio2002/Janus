// This file is named to sort after every other example file (zconstructs.go and zstr.go
// included), so that adding it leaves the addresses of the earlier example functions unchanged
// (some audit fixtures name them).

package basic

// The second batch of language-construct examples (docs/COVERAGE.md, section 3, package M1):
// conversions between integers and floating point and between float32 and float64, the
// nil-dereference fault, a range-over-func loop whose iterator and loop body are real calls,
// and the float and string forms of the min and max builtins. Each has a theorem on arm64
// (examples/proofs/<Name>.lean) and on amd64 (examples/proofs-amd64/<Name>/Proof.lean).

// I64ToF64 converts x to float64, rounding to nearest-even when |x| >= 2^53 (SCVTF on arm64,
// CVTSQ2SD on amd64).
//
//go:noinline
func I64ToF64(x int64) float64 { return float64(x) }

// F64ToI64 converts x to int64, truncating toward zero. Out of range the result is
// implementation-specific: arm64 (FCVTZS) saturates to -2^63 or 2^63-1 and maps NaN to 0, amd64
// (CVTTSD2SQ) gives the integer indefinite 0x8000000000000000.
//
//go:noinline
func F64ToI64(x float64) int64 { return int64(x) }

// U64ToF64 converts x to float64 (UCVTF on arm64; on amd64, which has no unsigned conversion,
// CVTSQ2SD directly below 2^63 and otherwise of x/2 with the lost bit or-ed back in, doubled).
//
//go:noinline
func U64ToF64(x uint64) float64 { return float64(x) }

// F64ToF32 rounds x to float32 (FCVT on arm64, CVTSD2SS on amd64).
//
//go:noinline
func F64ToF32(x float64) float32 { return float32(x) }

// F32ToF64 widens x to float64, exactly (FCVT on arm64, CVTSS2SD on amd64).
//
//go:noinline
func F32ToF64(x float32) float64 { return float64(x) }

// LoadThird returns p[2]. Go emits no explicit nil check for it: a nil p makes the load itself
// fault, at address 16, inside the unmapped first page, and the runtime's signal handler turns
// the fault into a nil-pointer panic.
//
//go:noinline
func LoadThird(p *[4]uint64) uint64 { return p[2] }

// Span is the half-open interval [Lo, Hi) of integers.
type Span struct{ Lo, Hi uint64 }

// All calls yield on Lo, Lo+1, ..., Hi-1 in order, until yield returns false: a push iterator
// (iter.Seq[uint64]) that stays a real call.
//
//go:noinline
func (r Span) All(yield func(uint64) bool) {
	for i := r.Lo; i < r.Hi; i++ {
		if !yield(i) {
			return
		}
	}
}

// SpanSum returns lo + (lo+1) + ... + (hi-1) (mod 2^64), by range over the iterator Span.All.
// The loop body becomes the closure SpanSum-range1, which All calls through its funcval; the
// closure updates the sum and the loop state in SpanSum's frame and checks the state
// (runtime.panicrangestate when the iterator misbehaves).
//
//go:noinline
func SpanSum(lo, hi uint64) uint64 {
	var s uint64
	for x := range (Span{lo, hi}).All {
		s += x
	}
	return s
}

// MinF64 returns min(a, b): a NaN if either is a NaN, and -0 for a zero of each sign.
//
//go:noinline
func MinF64(a, b float64) float64 { return min(a, b) }

// MaxF64 returns max(a, b): a NaN if either is a NaN, and +0 for a zero of each sign.
//
//go:noinline
func MaxF64(a, b float64) float64 { return max(a, b) }

// MinStr returns the lexically smaller of s and t (bytewise, as runtime.cmpstring compares).
//
//go:noinline
func MinStr(s, t string) string { return min(s, t) }
