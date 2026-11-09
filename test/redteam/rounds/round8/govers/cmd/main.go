// Round 8 G3: Add calls lib.Zero (returns 0). Built with go1.25 and labelled go1.26 with
// -ldflags=-X runtime.buildVersion=go1.26.0. Prints Add(1, 2) = 3.
package main

import (
	"fmt"
	"os"

	"example.com/govers/lib"
)

//go:noinline
func Add(x, y uint64) uint64 { return x + y + lib.Zero() }

func main() { fmt.Println(Add(uint64(len(os.Args)), 2)) }
