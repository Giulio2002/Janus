package main

import (
	"os"

	"example.com/basic"
)

// The panic examples (examples/basic/rtpanic.go): kept alive through Keep, and called once on
// inputs that neither panic nor fault.
func init() {
	Keep = append(Keep, basic.PanicIf, basic.DeferInc, basic.RecoverSet, basic.IndexAt,
		basic.LoadField, basic.DeferLoop, basic.Counter)
	n := uint64(len(os.Args))
	var c uint64
	basic.DeferLoop(basic.Counter(&c), int(n))
	println(basic.PanicIf(n), basic.DeferInc(&c, n), basic.RecoverSet(n),
		basic.IndexAt([]uint64{1, 2, 3}, int(n)-1), basic.LoadField(&basic.Cell{V: n}), c)
}
