package main

import (
	"fmt"

	"example.com/cgo"
)

func main() {
	var w uint64
	cgo.Store(&w, 7)
	fmt.Println(cgo.Add(2, 3), cgo.Sum([]uint64{1, 2, 3}), w, cgo.Count([]byte("abca"), 97))
}
