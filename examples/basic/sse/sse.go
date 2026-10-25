//go:build amd64

// Package sse holds the WP-D examples: Go functions whose work is done by small Go assembly
// functions using SSE2/SSE4.2 (built into artifacts/examples-amd64-sse, a binary of its own so
// that the other examples' binary does not change).
package sse

// indexByte32 returns the index of the first byte of *p equal to c, or 32 if there is none:
// two PCMPEQB/PMOVMSKB masks against c broadcast with PUNPCKLBW/PSHUFLW/PUNPCKLQDQ, then BSF.
//
//go:noescape
func indexByte32(p *[32]byte, c byte) int

// crc32cBlock updates the CRC-32C register crc with the 16 bytes of *p (two CRC32Q).
//
//go:noescape
func crc32cBlock(crc uint32, p *[16]byte) uint32

// Index32 returns the index of the first byte of *p equal to c, or 32 if there is none.
//
//go:noinline
func Index32(p *[32]byte, c byte) int { return indexByte32(p, c) }

// CRC32C16 returns the CRC-32C (Castagnoli) checksum crc updated with the 16 bytes of *p, as
// hash/crc32.Update(crc, crc32.MakeTable(crc32.Castagnoli), p[:]) does.
//
//go:noinline
func CRC32C16(crc uint32, p *[16]byte) uint32 { return ^crc32cBlock(^crc, p) }
