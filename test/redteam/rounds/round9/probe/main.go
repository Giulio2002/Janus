// Command probe9 calls the heap-allocation examples (examples/basic/zalloc.go) the way real
// Go code does, so that audit/round9/probe/*.py can stop at the calls under gdb (amd64) or
// qemu's gdb stub (arm64) and check the theorems' hypotheses against the real runtime state.
//
//	probe9 loop N   N rounds of NewPair/MakeSlice/AppendOne/SetNext
//	probe9 loopgc N the same with a GC cycle running most of the time (write barrier on)
//	probe9 strcat N N string concatenations of 64 bytes (mallocgc(64, nil, false), the MallocFast case)
//	probe9 mcache N MallocFast's MCacheOK, evaluated in-process before N 64-byte requests (arm64)
//	probe9 hdr N    addresses mod 16 of N pointerful 528-byte objects (malloc header: 8)
//	probe9 grow K   the capacities AppendOne (runtime.growslice) chooses up to K elements
//	probe9 maps N   small-map lookups (basic.Lookup) on the main and 8 other goroutines
//	probe9 big K    MakeSlice(1<<K): a request the allocation contracts admit (8·2^K ≤ 2^48)
package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"strings"
	"unsafe"

	"example.com/basic"
)

var sink []*basic.Node
var strSink string
var mapSink uint64
var hdrSink []*[66]*int

func main() {
	if len(os.Args) < 3 {
		fmt.Println("usage: probe9 loop N | big K")
		os.Exit(2)
	}
	k, _ := strconv.Atoi(os.Args[2])
	switch os.Args[1] {
	case "hdr":
		// a pointerful 528-byte object (> 512: Go 1.26 puts an 8-byte malloc header before it)
		for i := 0; i < k; i++ {
			p := new([66]*int)
			hdrSink = append(hdrSink, p) // escapes: runtime.newobject
			fmt.Println(uintptr(unsafe.Pointer(p)) % 16)
		}
	case "grow":
		// every capacity append(s, x) chooses for []uint64 from empty up to K elements:
		// "newLen oldCap newCap" per growth
		var s []uint64
		for i := 0; i < k; i++ {
			c := cap(s)
			s = basic.AppendOne(s, uint64(i))
			if cap(s) != c {
				fmt.Println(len(s), c, cap(s))
			}
		}
	case "maps":
		// small maps looked up from the main goroutine and from fresh goroutines
		// (audit/round9/probe/maps_amd64.py checks smallModel's heap interval at each call)
		done := make(chan bool)
		for j := 0; j < 8; j++ {
			go func(j int) {
				m := map[uint64]uint64{uint64(j): 1, 7: 2}
				var acc uint64
				for i := 0; i < k; i++ {
					v, _ := basic.Lookup(m, uint64(i%9))
					acc += v
				}
				mapSink += acc
				done <- true
			}(j)
		}
		m := map[uint64]uint64{1: 1, 2: 4}
		for i := 0; i < k; i++ {
			v, _ := basic.Lookup(m, uint64(i%5))
			mapSink += v
		}
		for j := 0; j < 8; j++ {
			<-done
		}
		fmt.Println("ok", mapSink)
	case "mcache":
		mcacheProbe(k)
	case "strcat":
		a, b := strings.Repeat("a", 32), strings.Repeat("b", 32)
		n := 0
		for i := 0; i < k; i++ {
			c := a + b
			strSink = c
			n += len(c)
			basic.AppendOne(nil, uint64(i)) // keeps the probes' start marker (AppendOne) reachable here
		}
		fmt.Println("ok", n)
	case "big":
		s := basic.MakeSlice(1 << k)
		fmt.Println("returned", len(s))
	case "loop", "loopgc":
		done := make(chan bool)
		go func() {
			if os.Args[1] == "loop" {
				return
			} // keep a GC cycle (and so the write barrier) running most of the time
			for {
				select {
				case <-done:
					return
				default:
					runtime.GC()
				}
			}
		}()
		var s []uint64
		var acc uint64
		for i := 0; i < k; i++ {
			n, q := &basic.Node{Val: uint64(i)}, &basic.Node{}
			basic.SetNext(n, q)
			sink = append(sink, n)
			if len(sink) > 4096 {
				sink = sink[:0]
			}
			p := basic.NewPair(uint64(i), uint64(i+1))
			m := basic.MakeSlice(i % 40)
			s = basic.AppendOne(s, uint64(i))
			if len(s) > 100000 {
				s = nil
			}
			acc += p.A + uint64(len(m))
		}
		close(done)
		fmt.Println("ok", acc, len(s))
	}
}
