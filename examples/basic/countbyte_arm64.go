package basic

import "unsafe"

// vCount is the AAPCS64 machine code that gcc -O2 auto-vectorises a C byte-count loop into
// (countbyte_arm64.s), behind an ABI0 shim.
//
//go:noescape
func vCount(p *byte, n uint64, c byte) uint64

// A64CountByte returns the number of bytes of b equal to c, computed by the gcc -O2
// auto-vectorised C loop of vCount (CMEQ/AND/ZIP1/ZIP2/UADDW/UADDW2/ADDP over 16-byte
// blocks, then a scalar tail).
//
//go:noinline
func A64CountByte(b []byte, c byte) int {
	return int(vCount(unsafe.SliceData(b), uint64(len(b)), c))
}
