// Package lib is an ordinary package with two Go-assembly functions (zero_arm64.s) whose linker
// symbols are in the runtime namespace: runtime·panicJanusR7 returns normally, and
// runtime·morestackJanusR7 panics. Round 7 G1 (docs/AUDIT-ROUND7.md).
package lib

// Zero returns 0, through runtime·panicJanusR7.
func Zero() uint64

// Boom panics, through runtime·morestackJanusR7.
func Boom() uint64

func boom() { panic("boom") }
