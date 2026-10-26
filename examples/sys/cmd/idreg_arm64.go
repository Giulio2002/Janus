package main

import "example.com/sys"

// keep every feature-ID read linked (janus extract needs the functions)
func init() {
	println(sys.AESField(), sys.SVEField(), sys.ISAR1(), sys.ZFR0(), sys.MMFR0())
}
