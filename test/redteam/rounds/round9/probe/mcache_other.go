//go:build !arm64

package main

func mcacheProbe(n int) { panic("probe9 mcache: arm64 only") }
