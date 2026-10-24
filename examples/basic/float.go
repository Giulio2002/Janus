package basic

import "math"

// AddF64 returns the IEEE 754 binary64 sum a + b. Go compiles it to one FADDD (arm64) or
// ADDSD (amd64), so the result is rounded by the current mode (FPCR.RMode / MXCSR.RC).
//
//go:noinline
func AddF64(a, b float64) float64 { return a + b }

// Dot3 returns the dot product a0*b0 + a1*b1 + a2*b2. On arm64 Go fuses the multiply-adds
// (FMULD, then two FMADDD: each addition and the multiplication before it are rounded once);
// on amd64 (GOAMD64=v1, no FMA) it computes three MULSD and two ADDSD, each rounded.
//
//go:noinline
func Dot3(a0, a1, a2, b0, b1, b2 float64) float64 { return a0*b0 + a1*b1 + a2*b2 }

// F64ToU64 converts x to uint64, truncating toward zero. The Go spec leaves out-of-range
// conversions implementation-defined: arm64 (FCVTZU) saturates and maps NaN to 0, amd64 uses
// CVTTSD2SQ around a comparison with 2^63.
//
//go:noinline
func F64ToU64(x float64) uint64 { return uint64(x) }

// Abs returns |x| by clearing the sign bit of its IEEE 754 encoding.
//
//go:noinline
func Abs(x float64) float64 { return math.Float64frombits(math.Float64bits(x) &^ (1 << 63)) }
