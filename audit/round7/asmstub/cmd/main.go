package main

import (
	"fmt"
	"os"

	"example.com/asmstub/lib"
)

//go:noinline
func Add(x, y uint64) uint64 { return x + y + lib.Zero() }

func main() { fmt.Println(Add(uint64(len(os.Args)), 2)) }
