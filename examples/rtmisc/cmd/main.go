// Command cmd links every rtmisc example (scripts/build-examples-rtmisc.sh).
package main

import (
	"unsafe"

	"example.com/rtmisc"
	"example.com/rtmisc/checkptr"
	"example.com/rtmisc/cover"
	"example.com/rtmisc/soft"
)

var sink uint64

func main() {
	println(real(rtmisc.Div(1, 2i)), rtmisc.Pop(7), rtmisc.AddAtomic(&sink, 1), rtmisc.BoxByte(3) != nil,
		rtmisc.ZeroBox() != nil, rtmisc.LoadKeep(&sink))
	println(cover.Clamp(5, 3), soft.Widen(0x3f800000), soft.Narrow(0x3ff0000000000000), soft.Mul(1, 2))
	println(checkptr.Word(unsafe.Pointer(&sink)))
}
