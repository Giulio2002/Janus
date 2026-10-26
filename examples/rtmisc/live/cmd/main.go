// Command cmd links the live-allocation examples (scripts/build-examples-rtmisc.sh).
package main

import "example.com/rtmisc/live"

func main() {
	a, b, c := live.Three(2, 7)
	println(a[0], b[1], c.P != nil, len(live.Rows(3, 2)))
	d, s2 := make([]uint64, 2), []uint64{1, 2}
	bx := new(live.Box)
	live.Chain(d, s2, bx, 2)
	println(d[0], bx.P != nil)
}
