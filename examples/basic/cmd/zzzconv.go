package main

import "example.com/basic"

// The live boxing example (examples/basic/zzzconv.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.BoxAfterNew)
}
