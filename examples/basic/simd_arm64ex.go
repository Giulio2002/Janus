package basic

import "bytes"

// The functions below reach the runtime's SIMD routines (internal/bytealg, runtime.memequal).
// Their names start with A64 because the arm64 proofs are about them.

// A64Equal64 reports whether two 64-byte arrays hold the same bytes. bytes.Equal compiles to a
// length comparison (constant here) and a call of runtime.memequal, whose arm64 version
// compares 64-byte chunks with LD1/CMEQ/AND/UMOV.
//
//go:noinline
func A64Equal64(a, b *[64]byte) bool { return bytes.Equal(a[:], b[:]) }

// A64IndexByte returns the index of the first c in b, or -1. bytes.IndexByte calls
// internal/bytealg.IndexByte, whose arm64 version scans 32-byte chunks with
// DUP/LD1/CMEQ/ORR/ADDP/AND/UMOV.
//
//go:noinline
func A64IndexByte(b []byte, c byte) int { return bytes.IndexByte(b, c) }
