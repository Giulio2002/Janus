// Command mxcsr prints MXCSR (amd64) / FPCR and FPSR (arm64) as a Go program sees it (docs/AUDIT-FP.md, row X64-MXCSR-STICKY):
// at the start of main, and after one inexact float64 addition. The example theorems' former
// precondition `s.mxcsr = 0x1F80` requires every status flag (bits 5:0) to be clear.
package main

import (
	"fmt"
	"os"
	"strconv"
)

func stmxcsr() uint32

//go:noinline
func add(a, b float64) float64 { return a + b }

func main() {
	start := stmxcsr()
	a, _ := strconv.ParseFloat(os.Args[1], 64)
	b, _ := strconv.ParseFloat(os.Args[2], 64)
	r := add(a, b)
	after := stmxcsr()
	fmt.Printf("main-entry=%#x after-add=%#x sum=%v%s\n", start, after, r, extra())
}
