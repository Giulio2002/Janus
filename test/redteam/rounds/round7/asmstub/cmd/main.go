// Round 7 G1: Add calls lib.Zero (returns 0) and Inc calls lib.Boom (panics). Prints Add(1, 2),
// and lib.Label() (42), then calls Inc(1), which panics with "boom".
package main

import (
	"fmt"
	"os"

	"example.com/asmstub/lib"
)

//go:noinline
func Add(x, y uint64) uint64 { return x + y + lib.Zero() }

//go:noinline
func Inc(x uint64) uint64 { return x + 1 + lib.Boom() }

func main() {
	fmt.Println(Add(uint64(len(os.Args)), 2), lib.Label())
	fmt.Println(Inc(uint64(len(os.Args))))
}
