//go:build amd64

// Package avx holds the WP-F examples: Go functions whose work is done by small Go assembly
// functions using AVX2 on YMM registers (built into artifacts/examples-amd64-avx, a binary of its
// own so that the other examples' binaries do not change).
package avx

// indexByte64 returns the index of the first byte of *p equal to c, or 64 if there is none:
// c broadcast to the 32 bytes of Y0 (VMOVD, VPBROADCASTB), two VPCMPEQB/VPMOVMSKB masks of the
// two 32-byte halves, joined into a 64-bit mask, TZCNT.
//
//go:noescape
func indexByte64(p *[64]byte, c byte) int

// maxU32x8 returns the largest of the eight words of *p: VEXTRACTI128 of the upper lane,
// VPMAXUD with the lower one, then two VPSHUFD/VPMAXUD steps, VMOVD.
//
//go:noescape
func maxU32x8(p *[8]uint32) uint32

// Index64 returns the index of the first byte of *p equal to c, or 64 if there is none.
//
//go:noinline
func Index64(p *[64]byte, c byte) int { return indexByte64(p, c) }

// MaxU32x8 returns the largest of the eight words of *p.
//
//go:noinline
func MaxU32x8(p *[8]uint32) uint32 { return maxU32x8(p) }
