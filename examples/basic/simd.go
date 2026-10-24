package basic

import "bytes"

// The vector-path examples: functions whose work is done by the AVX2 (or SSE) code of the Go
// runtime, depending on the CPU-feature globals the runtime sets at start-up.

// Equal64 compares two 64-byte arrays with bytes.Equal, which the compiler lowers to a call
// of runtime.memequal (internal/bytealg's memeqbody: 64 bytes per iteration with VPCMPEQB and
// VPMOVMSKB when internal/cpu.X86.HasAVX2 is set, with PCMPEQB and PMOVMSKB otherwise).
//
//go:noinline
func Equal64(a, b *[64]byte) bool { return bytes.Equal(a[:], b[:]) }

// CopyBlock512 copies a 512-byte array with copy(), which the compiler lowers to a call of
// runtime.memmove. Above 256 bytes memmove consults runtime.memmoveBits and, when AVX is
// available, takes its AVX path (32-byte VMOVDQU loads, 32-byte-aligned VMOVDQA stores).
//
//go:noinline
func CopyBlock512(dst, src *[64]uint64) { copy(dst[:], src[:]) }
