package basic

import (
	_ "hash/crc32"
	_ "unsafe" // go:linkname
)

// ieeeUpdate is hash/crc32's arm64 assembly kernel (crc32_arm64.s): it updates the
// non-inverted CRC-32 (IEEE polynomial, reflected) `crc` with the bytes of p, 16 bytes per
// iteration with two CRC32X, then the 8/4/2/1-byte tail with CRC32X/W/H/B. crc32.Update and
// crc32.ChecksumIEEE reach it through `^ieeeUpdate(^crc, p)` once cpu.ARM64.HasCRC32 is known.
//
//go:linkname ieeeUpdate hash/crc32.ieeeUpdate
func ieeeUpdate(crc uint32, p []byte) uint32

// A64Crc32 is crc32.Update(crc, crc32.IEEETable, p) on a CPU with the CRC32 instructions,
// without the sync.OnceFunc initialisation and the indirect call through the updateIEEE
// function variable: `^ieeeUpdate(^crc, p)`.
//
//go:noinline
func A64Crc32(crc uint32, p []byte) uint32 { return ^ieeeUpdate(^crc, p) }
