// Package soft is built with -gcflags=example.com/rtmisc/soft=-d=softfloat
// (scripts/build-examples-rtmisc.sh): every floating-point operation is a call of the
// runtime's software floating point (runtime/softfloat64.go). The functions take and return
// the IEEE 754 encodings, so that their arguments and results are in integer registers.
package soft

import "math"

// Widen is float64(float32): runtime.f32to64.
//
//go:noinline
func Widen(b uint32) uint64 { return math.Float64bits(float64(math.Float32frombits(b))) }

// Narrow is float32(float64): runtime.f64to32.
//
//go:noinline
func Narrow(b uint64) uint32 { return math.Float32bits(float32(math.Float64frombits(b))) }

// Mul is a float64 product: runtime.fmul64.
//
//go:noinline
func Mul(a, b uint64) uint64 {
	return math.Float64bits(math.Float64frombits(a) * math.Float64frombits(b))
}
