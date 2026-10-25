// Package asm holds the Go assembly examples of Janus (docs/ABI0.md): functions written in Go
// assembly (asm_arm64.s, asm_amd64.s), which use the ABI0 calling convention (arguments and
// results in the caller's frame), the Go functions that call them, and the ABI wrappers the
// toolchain generates between ABIInternal and ABI0.
//
// Every address a proof depends on comes from the binary scripts/build-examples-asm.sh builds
// (Go pinned there); the proofs in proofs/{arm64,amd64}/ name addresses only through the
// extraction.
package asm

// AddAsm returns x + y (mod 2^64). Assembly, ABI0: x at 0(FP), y at 8(FP), the result at
// 16(FP).
func AddAsm(x, y uint64) uint64

// XorSlice returns the XOR of the elements of xs. Assembly, ABI0: a loop over the slice whose
// header (base, len, cap) is at 0(FP), the result at 24(FP).
func XorSlice(xs []uint64) uint64

// Twice returns 2*x + 1. Assembly, ABI0, with a 16-byte frame: it calls the Go function double,
// which the assembler reaches through the ABI0-to-ABIInternal wrapper the compiler generates
// (double.abi0).
func Twice(x uint64) uint64

// double is called from assembly only (Twice).
//
//go:noinline
func double(x uint64) uint64 { return 2 * x }

// CallXor returns XorSlice(xs) ^ 1: Go code calling an assembly function of its own package,
// which the compiler compiles to a direct ABI0 call of XorSlice.abi0 (no wrapper).
//
//go:noinline
func CallXor(xs []uint64) uint64 { return XorSlice(xs) ^ 1 }
