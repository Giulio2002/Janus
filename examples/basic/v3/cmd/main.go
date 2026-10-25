// Command v3 keeps the GOAMD64=v3 example functions alive in the linked binary (see
// examples/basic/cmd).
package main

import (
	"os"

	"example.com/basic/v3"
)

// Keep references every example function as a func value.
var Keep = []any{v3.Fma, v3.BitMix, v3.LoadBE}

func main() {
	n := uint64(len(os.Args))
	var b [8]byte
	b[0] = byte(n)
	println(len(Keep), v3.Fma(float64(n), 2, 3), v3.BitMix(n, n+1, uint(n)), v3.LoadBE(&b))
}
