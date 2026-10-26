package main

import "example.com/sys"

// Command idregcmd links the feature-ID register examples (a binary of its own: the other kernel
// examples' proofs name addresses of examples-sys-arm64, which this code would shift).
func main() {
	println(sys.AESField(), sys.SVEField(), sys.ISAR1(), sys.ZFR0(), sys.MMFR0())
}
