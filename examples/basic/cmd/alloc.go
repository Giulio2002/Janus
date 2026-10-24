package main

import "example.com/basic"

// The heap-allocation examples (examples/basic/alloc.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.NewPair, basic.MakeSlice, basic.AppendOne, basic.SetNext)
}
