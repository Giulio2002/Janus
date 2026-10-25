// Command asm keeps every example function of example.com/asm alive in the linked binary (the
// linker drops unreferenced functions). Storing the assembly functions as func values also makes
// the compiler emit their ABIInternal wrappers (example.com/asm.XorSlice, ...), which the
// wrapper theorems are about.
package main

import (
	"os"

	"example.com/asm"
)

// Keep references every example function as a func value.
var Keep = []any{asm.AddAsm, asm.XorSlice, asm.Twice, asm.CallXor}

func main() {
	n := uint64(len(os.Args))
	xs := []uint64{n, n + 1, n + 2}
	println(asm.AddAsm(n, 2), asm.XorSlice(xs), asm.Twice(n), asm.CallXor(xs), len(Keep))
}
