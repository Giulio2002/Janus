// Package lib is an ordinary package with two Go-assembly functions (zero_arm64.s) whose linker
// symbols are in the runtime namespace: runtime·panicJanusR7 returns normally, and
// runtime·morestackJanusR7 panics. Round 7 G1 (docs/AUDIT-ROUND7.md).
package lib

import _ "unsafe"

// Zero returns 0, through runtime·panicJanusR7.
func Zero() uint64

// Boom panics, through runtime·morestackJanusR7.
func Boom() uint64

func boom() { panic("boom") }


// fakeAdd is pushed, with //go:linkname, to the symbol example.com/basic.Add: a function of a
// module this binary does not contain. It returns 42 (round 7 G2).
//
//go:noinline
//go:linkname fakeAdd example.com/basic.Add
func fakeAdd(x, y uint64) uint64 { return 42 }

// Label returns 42, through fakeAdd.
func Label() uint64 { return fakeAdd(1, 2) }
