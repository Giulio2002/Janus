package main

import "example.com/basic"

// The mutual-recursion and writable-global examples (examples/basic/zmutual.go): kept alive
// through Keep.
func init() {
	Keep = append(Keep, basic.IsEven, basic.IsOdd, basic.CycA, basic.CycB, basic.CycC, basic.MulAlgo, basic.Double, basic.TuningCut)
}
