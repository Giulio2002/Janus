package main

import "example.com/basic"

// The equality, hashing and typed-memory examples (examples/basic/rteq.go): kept alive through
// Keep. The maps make the linker keep the runtime's fixed-size hash functions (memhash0, 8, 16,
// memhash_varlen) and memequal_varlen, whose machine code the Alg* proofs verify.
func init() {
	Keep = append(Keep, basic.Eq32, basic.StrEq, basic.F64Eq, basic.CopyTrees, basic.ClearTrees,
		basic.LookupStr, basic.LookupFKey,
		map[struct{}]bool{}, map[uint8]bool{}, map[uint16]bool{}, map[[3]byte]bool{})
}
