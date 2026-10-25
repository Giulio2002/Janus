// Command cmd is the example binary of package avx (artifacts/examples-amd64-avx).
package main

import (
	"fmt"

	"example.com/basic/avx"
)

func main() {
	var b [64]byte
	b[41] = 'x'
	w := [8]uint32{3, 9, 1, 0xfffffff0, 7, 2, 8, 5}
	fmt.Println(avx.Index64(&b, 'x'), avx.MaxU32x8(&w))
}
