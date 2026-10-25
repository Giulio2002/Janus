package main

import "example.com/basic"

// The second batch of language-construct examples (examples/basic/zzconstructs2.go): kept
// alive through Keep.
func init() {
	Keep = append(Keep, basic.I64ToF64, basic.F64ToI64, basic.U64ToF64, basic.F64ToF32,
		basic.F32ToF64, basic.LoadThird, basic.SpanSum, basic.MinF64, basic.MaxF64,
		basic.MinStr)
}
