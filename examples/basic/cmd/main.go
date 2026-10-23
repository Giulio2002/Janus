// Command basic keeps every example function alive in the linked binary so that
// `janus extract` can find it. The Go linker removes unreachable functions, so each
// one is both stored in a package-level table and called on inputs the compiler
// cannot constant-fold (derived from os.Args).
package main

import (
	"os"

	"example.com/basic"
)

// Keep references every example function as a func value.
var Keep = []any{
	basic.Add,
	basic.Max,
	basic.Add128,
	basic.Mul64,
	basic.Sum,
	basic.Get,
	basic.Add256,
	basic.Div,
	basic.AddThree,
	basic.Table,
	basic.HexDigit,
	basic.SetOne256,
	basic.GlobalTable,
	basic.Bump,
}

func main() {
	n := uint64(len(os.Args))
	xs := make([]uint64, n+3)
	for i := range xs {
		xs[i] = uint64(i) * n
	}
	var z, x, y [4]uint64
	x[0], y[0] = n, ^uint64(0)
	basic.Add256(&z, &x, &y)
	var one [4]uint64
	basic.SetOne256(&one)
	hi, lo := basic.Add128(n, n+1, n+2, n+3)
	mh, ml := basic.Mul64(n<<40, n<<33)
	r := basic.Add(n, 2) ^ basic.Max(n, 4) ^ basic.Sum(xs) ^ basic.Get(xs, int(n)) ^
		basic.Div(100, n) ^ basic.AddThree(n, 1, 2) ^ hi ^ lo ^ mh ^ ml ^ z[0] ^ z[1] ^
		basic.Table(n) ^ uint64(basic.HexDigit(n)) ^ basic.GlobalTable(n) ^ basic.Bump(n) ^ one[0]
	println(r, len(Keep))
}
