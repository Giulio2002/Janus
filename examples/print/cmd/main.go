// Command print keeps every print example alive in the linked binary (janus extract needs the
// functions; the linker drops unreachable ones) and calls each once.
package main

import (
	"os"
	"unsafe"

	"example.com/print"
)

type str string

func (s str) String() string { return string(s) }

func main() {
	n := uint64(len(os.Args))
	print.PrintX(n)
	print.PrintBool(n > 0)
	print.PrintNeg()
	print.PrintStr("s")
	print.PrintInt(-int64(n))
	b := []byte("ab")
	print.PrintPtr(unsafe.Pointer(&b[0]))
	print.PrintUintptr(uintptr(n))
	print.PrintSlice(b)
	print.PrintEface(n)
	print.PrintIface(str("x"))
	print.PrintF64(float64(n) / 3)
	print.PrintF32(float32(n) / 3)
	print.PrintC128(complex(float64(n), -1))
	print.PrintC64(complex(float32(n), 2))
}
