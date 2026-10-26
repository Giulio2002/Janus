// Package softcheck tests the runtime's software floating point (runtime/softfloat64.go) against
// IEEE 754 binary64 hardware arithmetic, to justify the preconditions of the Lean contracts
// Janus.Contracts.SoftFloat (docs/RUNTIME-CONTRACTS.md, "Soft float").
//
// The functions under test are the runtime's own (//go:linkname), so build with
// -ldflags=-checklinkname=0 (scripts/softfloat-check.sh does).
package softcheck

import (
	"math"
	"math/big"
	"math/rand/v2"
	_ "unsafe" // for go:linkname
)

//go:linkname fadd64 runtime.fadd64
func fadd64(f, g uint64) uint64

//go:linkname fsub64 runtime.fsub64
func fsub64(f, g uint64) uint64

//go:linkname fmul64 runtime.fmul64
func fmul64(f, g uint64) uint64

//go:linkname fdiv64 runtime.fdiv64
func fdiv64(f, g uint64) uint64

const (
	signBit = 1 << 63
	expMask = 0x7FF
	fracLen = 52
)

func isNaN(x uint64) bool  { return x>>fracLen&expMask == expMask && x&(1<<fracLen-1) != 0 }
func isInf(x uint64) bool  { return x>>fracLen&expMask == expMask && x&(1<<fracLen-1) == 0 }
func isZero(x uint64) bool { return x&^signBit == 0 }

// finiteNonzero reports whether x is a nonzero subnormal or normal number.
func finiteNonzero(x uint64) bool { return !isNaN(x) && !isInf(x) && !isZero(x) }

// rat is the exact value of a finite binary64.
func rat(x uint64) *big.Rat {
	r := new(big.Rat)
	r.SetFloat64(math.Float64frombits(x))
	return r
}

// minNormal is 2^-1022.
var minNormal = new(big.Rat).SetFrac(big.NewInt(1), new(big.Int).Lsh(big.NewInt(1), 1022))

// Tiny reports whether the exact result q of an operation on two finite nonzero operands is
// nonzero and below 2^-1022 in magnitude (the Lean predicate "tinyBefore of the exact result").
func Tiny(q *big.Rat) bool {
	if q.Sign() == 0 {
		return false
	}
	a := new(big.Rat).Abs(q)
	return a.Cmp(minNormal) < 0
}

// ExactTiny is Tiny of the exact sum / product / quotient (op '+', '*', '/') of finite nonzero
// operands, and false when an operand is not finite nonzero (or the divisor is zero).
func ExactTiny(op byte, f, g uint64) bool {
	if !finiteNonzero(f) || !finiteNonzero(g) {
		return false
	}
	a, b := rat(f), rat(g)
	switch op {
	case '+':
		return Tiny(new(big.Rat).Add(a, b))
	case '*':
		return Tiny(new(big.Rat).Mul(a, b))
	default:
		return Tiny(new(big.Rat).Quo(a, b))
	}
}

// IEEE is the round-to-nearest-even result of the hardware.
func IEEE(op byte, f, g uint64) uint64 {
	a, b := math.Float64frombits(f), math.Float64frombits(g)
	switch op {
	case '+':
		return math.Float64bits(a + b)
	case '-':
		return math.Float64bits(a - b)
	case '*':
		return math.Float64bits(a * b)
	default:
		return math.Float64bits(a / b)
	}
}

// Soft is the runtime's software result.
func Soft(op byte, f, g uint64) uint64 {
	switch op {
	case '+':
		return fadd64(f, g)
	case '-':
		return fsub64(f, g)
	case '*':
		return fmul64(f, g)
	default:
		return fdiv64(f, g)
	}
}

// Agree: the same encoding, or both NaN (which NaN is not specified).
func Agree(a, b uint64) bool { return a == b || (isNaN(a) && isNaN(b)) }

var fracPatterns = []uint64{0, 1, 2, 3, 1<<fracLen - 1, 1<<fracLen - 2, 1 << (fracLen - 1), 1<<(fracLen-1) + 1,
	1<<(fracLen-1) - 1, 0x5555555555555, 0xAAAAAAAAAAAAA & (1<<fracLen - 1), 1 << 26, 1<<26 - 1, 1<<27 + 1}

// Operand draws an operand: zeros, subnormals, exponents near the ends of the range and near
// 1, infinities, NaNs (quiet and signalling, with payloads), with special and random fractions.
func Operand(r *rand.Rand) uint64 {
	var frac uint64
	if r.IntN(2) == 0 {
		frac = fracPatterns[r.IntN(len(fracPatterns))]
	} else {
		frac = r.Uint64() & (1<<fracLen - 1)
	}
	if r.IntN(4) == 0 { // a few leading zeros / few bits set: subnormal-like or exactly small
		frac >>= r.IntN(fracLen + 1)
	}
	var e uint64
	switch k := r.IntN(20); {
	case k < 2:
		e = 0 // zero or subnormal
	case k < 5:
		e = 1 + uint64(r.IntN(60)) // just above the subnormal range
	case k < 7:
		e = 2046 - uint64(r.IntN(60)) // just below overflow
	case k == 7:
		e = 2047 // infinity or NaN
	case k < 11:
		e = 1023 - 70 + uint64(r.IntN(140)) // around 1
	default:
		e = 1 + uint64(r.IntN(2046))
	}
	x := e<<fracLen | frac
	if r.IntN(2) == 0 {
		x |= signBit
	}
	return x
}

// Result counts one run.
type Result struct {
	Cases        int
	Checked      int // cases the contract covers (not ExactTiny)
	Tiny         int // cases with a tiny exact result
	TinyMismatch int // of those, the runtime's result differs from IEEE
	Bad          []string
}

// Run draws n pairs per operation and compares the runtime with IEEE.
func Run(op byte, n int, seed uint64) Result {
	r := rand.New(rand.NewPCG(seed, uint64(op)))
	var res Result
	for i := 0; i < n; i++ {
		f, g := Operand(r), Operand(r)
		// near-cancellation and near-equal / near-reciprocal pairs
		switch r.IntN(8) {
		case 0:
			g = f ^ uint64(r.IntN(8))
			if op == '+' || op == '-' {
				g ^= signBit
			}
		case 1:
			g = f&^(1<<fracLen-1) ^ (r.Uint64() & (1<<fracLen - 1))
		}
		res.Cases++
		want, got := IEEE(op, f, g), Soft(op, f, g)
		tinyOp := op
		gg := g
		if op == '-' {
			tinyOp, gg = '+', g^signBit
		}
		tiny := ExactTiny(tinyOp, f, gg)
		if tiny {
			res.Tiny++
			if !Agree(want, got) {
				res.TinyMismatch++
			}
			continue
		}
		res.Checked++
		if !Agree(want, got) && len(res.Bad) < 20 {
			res.Bad = append(res.Bad, fmtCase(op, f, g, want, got))
		}
	}
	return res
}
