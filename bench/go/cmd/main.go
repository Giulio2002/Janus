// Command bench keeps every benchmark function alive in the linked binary (see
// examples/basic/cmd for the same pattern).
package main

import (
	"os"

	"example.com/bench"
)

var Keep = []any{
	bench.MulAdd8,
	bench.MulAdd8x3,
	bench.Nested,
	bench.Chain1,
	bench.Alias4,
	bench.BigFrame,
}

func main() {
	n := uint64(len(os.Args))
	var z, x [8]uint64
	x[0], z[1] = n, n+1
	r := bench.MulAdd8(&z, &x, n, n+2)
	var z1, z2 [8]uint64
	q0, q1, q2 := bench.MulAdd8x3(&z, &z1, &z2, &x, n, n+1, n+2)
	r ^= q0 ^ q1 ^ q2 ^ z1[3] ^ z2[4]
	r ^= bench.Nested(n, n+1) ^ bench.Chain1(n)
	a, b, c, d := n, n+1, n+2, n+3
	bench.Alias4(&a, &b, &c, &d)
	r ^= a ^ b ^ c ^ d ^ bench.BigFrame(n, n+5)
	println(r, len(Keep))
}
