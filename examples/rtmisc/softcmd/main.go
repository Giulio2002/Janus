// Command softcmd links the soft-float examples and runtime.KeepAlive (scripts/build-examples-rtmisc.sh).
package main

import (
	"runtime"

	"example.com/rtmisc/softf"
)

var sink uint64

// keep makes the linker keep the function runtime.KeepAlive (every direct use is the compiler
// intrinsic, which is no call).
var keep = runtime.KeepAlive

func main() {
	println(softf.Add(1, 2), softf.Mul(5, 6), softf.Div(7, 8))
	keep(&sink)
}
