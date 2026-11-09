package main

import (
	"os"
	"strconv"
)

// `probe9 mcache-init N` runs the MCacheOK probe during package initialisation, when the Go
// runtime keeps the main goroutine locked to the main thread's m (runtime.m0): every sampled
// call is then one MallocFast's shipped MCacheOK excluded (round 9 M1), deterministically.
func init() {
	if len(os.Args) == 3 && os.Args[1] == "mcache-init" {
		n, _ := strconv.Atoi(os.Args[2])
		mcacheProbe(n)
		os.Exit(0)
	}
}
