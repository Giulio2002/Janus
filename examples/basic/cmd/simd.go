package main

import "example.com/basic"

// The vector-path examples (examples/basic/simd.go): kept alive through Keep, which main
// prints.
func init() {
	Keep = append(Keep, basic.Equal64, basic.CopyBlock512)
}
