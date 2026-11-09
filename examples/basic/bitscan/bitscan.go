// Package bitscan holds the examples of the bit-scan instructions that math/bits compiles to:
// at GOAMD64=v1 `bits.Len64`, `bits.TrailingZeros64` and friends are BSR/BSF plus a CMOV/SETcc
// that reads ZF after the scan (ZF = 1 iff the source is zero; the destination of a zero scan is
// architecturally undefined), at GOAMD64=v3 they are LZCNT/TZCNT. Built twice
// (scripts/build/build-examples-amd64.sh): once per level, into binaries of their own so that the
// other example binaries do not change.
package bitscan

import "math/bits"

// BitLen64 returns bits.Len64(x): the position of the highest set bit plus one, 0 for 0.
//
//go:noinline
func BitLen64(x uint64) uint64 { return uint64(bits.Len64(x)) }

// TrailingZeros64 returns bits.TrailingZeros64(x): the index of the lowest set bit, 64 for 0.
//
//go:noinline
func TrailingZeros64(x uint64) uint64 { return uint64(bits.TrailingZeros64(x)) }

// ByteLen returns (bits.Len64(x)+7)/8, the number of bytes of x without leading zero bytes.
//
//go:noinline
func ByteLen(x uint64) uint64 { return uint64(bits.Len64(x)+7) / 8 }

// BitLen32 returns bits.Len32(x).
//
//go:noinline
func BitLen32(x uint32) uint64 { return uint64(bits.Len32(x)) }
