package main

import "example.com/basic"

// The arm64-only example of the gcc -O2 auto-vectorised C loop (examples/basic/countbyte_arm64.s).
func init() {
	Keep = append(Keep, basic.A64CountByte)
}
