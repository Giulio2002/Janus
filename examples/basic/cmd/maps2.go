package main

import "example.com/basic"

// The R3 map examples (examples/basic/maps2.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.LookupS, basic.InsertS, basic.DeleteS, basic.LookupK24,
		basic.InsertK24, basic.Has32, basic.Set32, basic.InsertPtr, basic.LookupPtr, basic.MakeHint)
}
