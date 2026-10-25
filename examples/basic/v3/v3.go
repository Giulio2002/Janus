// Package v3 holds the examples that exercise the GOAMD64=v3 instruction-set extensions: the
// Go compiler emits BMI1/BMI2, MOVBE and FMA3 for them when it may assume an x86-64-v3 CPU.
// They are built (scripts/build-examples-amd64.sh) only for linux/amd64 with GOAMD64=v3, into
// a binary of their own, so that the v1 and arm64 example binaries do not change.
package v3

import (
	"encoding/binary"
	"math"
)

// Fma returns a*b + c rounded once (math.FMA). With GOAMD64=v3 it is one VFMADD231SD.
//
//go:noinline
func Fma(a, b, c float64) float64 { return math.FMA(a, b, c) }

// BitMix combines BMI1/BMI2 idioms: x &^ y (ANDN), x & (x-1) (BLSR), and a variable shift
// y << (n & 63) (SHLX).
//
//go:noinline
func BitMix(x, y uint64, n uint) uint64 { return (x &^ y) ^ (x & (x - 1)) ^ (y << (n & 63)) }

// LoadBE reads a big-endian uint64 (MOVBE with GOAMD64=v3).
//
//go:noinline
func LoadBE(b *[8]byte) uint64 { return binary.BigEndian.Uint64(b[:]) }
