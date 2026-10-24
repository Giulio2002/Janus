package main

import (
	"fmt"

	"example.com/cgo"
	"example.com/cgo/cabi"
)

func main() {
	var w uint64
	cgo.Store(&w, 7)
	fmt.Println(cgo.Add(2, 3), cgo.Sum([]uint64{1, 2, 3}), w)
	px, py := cabi.PMix(1, 2, 3, 4, 5)
	b0, b1, b2, b3 := cabi.Big(7, 3)
	fmt.Println(cabi.Stack10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10), cabi.FP(5, 2, 3), px, py, b0, b1, b2, b3,
		cabi.VSum8(1, 2, 3, 4, 5, 6, 7, 8))
}
