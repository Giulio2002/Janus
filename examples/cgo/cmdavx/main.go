// Command cmdavx is the cgo example binary whose C is compiled by clang at -O3 -march=x86-64-v3
// (examples-cgo-avx-amd64).
package main

import (
	"fmt"

	"example.com/cgo/avx"
)

func main() {
	fmt.Println(avx.Dot32([]uint32{1, 2, 3, 4, 5}, []uint32{6, 7, 8, 9, 10}))
}
