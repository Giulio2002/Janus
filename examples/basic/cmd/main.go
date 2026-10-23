package main

import (
	"fmt"
	"example.com/basic"
)

func main() {
	fmt.Println(basic.Add(1, 2), basic.Max(3, 4), basic.Sum([]uint64{1, 2, 3}))
}
