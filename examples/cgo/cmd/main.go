package main

import (
	"fmt"

	"example.com/cgo"
	"example.com/cgo/cabi"
	"example.com/cgo/neon"
)

func main() {
	var w uint64
	cgo.Store(&w, 7)
	fmt.Println(cgo.Add(2, 3), cgo.Sum([]uint64{1, 2, 3}), w)
	// 3 * 1.5 = 4.5 as x87 double-extended values (little-endian, 16 bytes each)
	a := [16]byte{8: 0, 7: 0xC0, 9: 0x40}
	b := [16]byte{7: 0xC0, 8: 0xFF, 9: 0x3F}
	var r [16]byte
	cgo.MulLD(&a, &b, &r)
	fmt.Println(r[:10], cgo.Switch(3, 10))
	px, py := cabi.PMix(1, 2, 3, 4, 5)
	b0, b1, b2, b3 := cabi.Big(7, 3)
	fmt.Println(cabi.Stack10(1, 2, 3, 4, 5, 6, 7, 8, 9, 10), cabi.FP(5, 2, 3), px, py, b0, b1, b2, b3,
		cabi.VSum8(1, 2, 3, 4, 5, 6, 7, 8))
	fmt.Println(neon.Count([]byte("abca"), 97))
}
