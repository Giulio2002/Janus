// Round 6 F3: Add calls an ordinary function that returns 0, so Add returns x + y.
package main

import (
	"fmt"
	"os"

	"runtime.panicky/lib"
)

//go:noinline
func Add(x, y uint64) uint64 { return x + y + lib.Zero() }

func main() { fmt.Println(Add(uint64(len(os.Args)), 2)) }
