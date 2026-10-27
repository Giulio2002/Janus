package main

import "example.com/basic"

// The sync.Pool example (examples/basic/zpool.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.ScratchSum, basic.StackGrow)
}
