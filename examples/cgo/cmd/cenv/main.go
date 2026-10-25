// Command cenv runs the C environment examples (examples/cgo/cenv).
package main

import (
	"fmt"

	"example.com/cgo/cenv"
)

func main() {
	var u uint32 = 41
	a, b := cenv.TLSAdd(3)
	s, n := cenv.Libc("janus")
	fmt.Println(cenv.Bump(2), a, b, cenv.ArgMin([]int64{5, -2, 7, -2}), s, n, cenv.SetJmp(0), cenv.SetJmp(4),
		cenv.Alloca(10), cenv.AtomicInc(&u), u, cenv.CallGo(20))
}
