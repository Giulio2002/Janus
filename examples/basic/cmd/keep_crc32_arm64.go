package main

import "example.com/basic"

// The arm64 CRC32 example (examples/basic/crc32_arm64.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.A64Crc32)
}
