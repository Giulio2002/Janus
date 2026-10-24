package main

import "example.com/basic"

// The string and slice examples (examples/basic/zstr.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.Concat, basic.ToBytes, basic.FromBytes, basic.SumRunes, basic.RuneLen,
		basic.AppendPoint, basic.CopyNodes)
}
