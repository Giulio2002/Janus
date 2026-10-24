// Package lib defines, in Go assembly, a function whose linker symbol lies in package runtime.
package lib

// Zero returns 0. Its body (zero_arm64.s) calls runtime·panicJanusR7, an assembly function of
// this package that is named like a Go panic stub and returns normally.
func Zero() uint64
