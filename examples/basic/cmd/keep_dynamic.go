package main

import (
	"os"

	"example.com/basic"
)

// The dynamic-call examples (examples/basic/dynamic.go): kept alive through Keep, and called
// once so that both itabs of basic.Hasher are in the binary.
func init() {
	Keep = append(Keep, basic.HashWith, basic.ApplyTwice, basic.HashTwice, basic.MapSum,
		basic.AffineSum, basic.DeferAdd)
	n := uint64(len(os.Args))
	m, r := &basic.MulHasher{K: n}, &basic.RotHasher{K: n}
	xs := []uint64{n, n + 1}
	println(basic.HashWith(m, n) ^ basic.HashWith(r, n) ^ basic.HashTwice(m, n) ^
		basic.AffineSum(xs, n, n+2) ^ basic.DeferAdd(n, 3))
}
