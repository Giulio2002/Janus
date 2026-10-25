// Command cmdclang is the cgo example binary built with CC=clang (examples-cgo-clang-amd64).
package main

import (
	"fmt"

	"example.com/cgo/vec"
)

func main() {
	fmt.Println(vec.Sum32([]int32{1, 2, 3, 4, 5, 6, 7, 8, 9, -10}))
}
