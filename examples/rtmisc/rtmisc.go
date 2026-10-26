// Package rtmisc holds the examples of the remaining runtime entry points (docs/COVERAGE.md,
// R9; docs/RUNTIME-CONTRACTS.md, "Remaining runtime"): complex division, CPU feature flags,
// the runtime's read-only data objects (staticuint64s, zeroVal) and runtime.KeepAlive. The
// instrumented builds are in the subpackages: cover (-cover), soft (-d=softfloat) and checkptr
// (-d=checkptr), all linked into the binary of ./cmd (scripts/build-examples-rtmisc.sh), and
// sc (GOEXPERIMENT=sizespecializedmalloc), a binary of its own.
package rtmisc

import (
	"math/bits"
	"runtime"
	"sync/atomic"
)

// Div is complex division: the compiler calls runtime.complex128div (runtime/complex.go),
// which is ordinary Go code and is executed by the proofs.
//
//go:noinline
func Div(n, m complex128) complex128 { return n / m }

// Pop is bits.OnesCount64. On amd64 (GOAMD64=v1) the compiler tests runtime.x86HasPOPCNT and
// takes either one POPCNT or a call of the portable math/bits.OnesCount64; on arm64 it is
// VCNT/UADDLV with no test.
//
//go:noinline
func Pop(x uint64) int { return bits.OnesCount64(x) }

// AddAtomic is atomic.AddUint64. On arm64 (GOARM64=v8.0) the compiler tests
// runtime.arm64HasATOMICS and takes either one LDADDAL or an LDAXR/STLXR retry loop; on amd64
// it is LOCK XADDQ with no test.
//
//go:noinline
func AddAtomic(p *uint64, d uint64) uint64 { return atomic.AddUint64(p, d) }

// BoxByte converts a byte to an interface: no allocation, the data word is
// &runtime.staticuint64s[b] (cmd/compile/internal/walk/convert.go).
//
//go:noinline
func BoxByte(b uint8) any { return b }

// ZeroBox converts a zero array to an interface: no allocation, the data word is
// &runtime.zeroVal (cmd/compile/internal/walk/order.go, the read-only zero value).
//
//go:noinline
func ZeroBox() any { return [4]uint64{} }

// LoadKeep reads *p and keeps p alive until after the read with runtime.KeepAlive, an
// intrinsic: no call, only the spill of p that keeps it live.
//
//go:noinline
func LoadKeep(p *uint64) uint64 {
	v := *p
	runtime.KeepAlive(p)
	return v
}
