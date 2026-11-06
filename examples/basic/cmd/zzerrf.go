package main

import "example.com/basic"

// The fmt.Errorf example (examples/basic/zzerrf.go): kept alive through Keep.
func init() {
	Keep = append(Keep, basic.ErrWrap)
}
