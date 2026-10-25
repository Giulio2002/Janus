package main

import "example.com/basic"

// The interface examples (examples/basic/iface.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.Box, basic.AsHasher, basic.Classify, basic.Equal)
}
