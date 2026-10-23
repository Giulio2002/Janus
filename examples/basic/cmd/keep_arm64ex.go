package main

import "example.com/basic"

// The arm64 SIMD examples (examples/basic/simd_arm64ex.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.A64Equal64, basic.A64IndexByte)
}
