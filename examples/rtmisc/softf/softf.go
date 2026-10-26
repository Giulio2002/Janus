// Package softf is built with -gcflags=example.com/rtmisc/softf=-d=softfloat
// (scripts/build-examples-rtmisc.sh): every floating-point operation is a call of the runtime's
// software floating point (runtime/softfloat64.go). The functions take and return the IEEE 754
// encodings, so that their arguments and results are in integer registers. They are the examples
// of the contracts Janus.Contracts.SoftFloat (docs/RUNTIME-CONTRACTS.md, "Soft float and
// KeepAlive"); runtime.KeepAlive, which the contract library also describes, is extracted and
// proved from its own code (softcmd links it through a function value). Package soft holds the older f32to64/f64to32/fmul64 examples (their binary is
// separate, so that no address of an earlier example changes).
package softf

import "math"

// Add is a float64 sum: runtime.fadd64.
//
//go:noinline
func Add(a, b uint64) uint64 {
	return math.Float64bits(math.Float64frombits(a) + math.Float64frombits(b))
}

// Mul is a float64 product: runtime.fmul64.
//
//go:noinline
func Mul(a, b uint64) uint64 {
	return math.Float64bits(math.Float64frombits(a) * math.Float64frombits(b))
}

// Div is a float64 quotient: runtime.fdiv64.
//
//go:noinline
func Div(a, b uint64) uint64 {
	return math.Float64bits(math.Float64frombits(a) / math.Float64frombits(b))
}
