// Round 10 probes against the real go1.26.0 runtime (docs/AUDIT-ROUND10.md).
// Build: go build -ldflags=-checklinkname=0 (linkname pulls of runtime internals).
//
//	probe10 tanil N    runtime.typeAssert with a nil type and CanFail (contract I1): how many of
//	                   N calls fault in buildTypeAssertCache(oldC, nil, nil)
//	probe10 convt N    runtime.convT64(v) for v >= 256, keeping every box (contract V3): how many
//	                   distinct fresh boxes N calls return, and the staticuint64s case
package main

import (
	"fmt"
	"os"
	"reflect"
	"strconv"
	"unsafe"
)

type taDesc struct {
	Cache   unsafe.Pointer
	Inter   unsafe.Pointer
	CanFail bool
}

//go:linkname typeAssert runtime.typeAssert
func typeAssert(s *taDesc, t unsafe.Pointer) unsafe.Pointer

//go:linkname convT64 runtime.convT64
func convT64(v uint64) unsafe.Pointer

//go:linkname emptyTypeAssertCache runtime.emptyTypeAssertCache
var emptyTypeAssertCache [3]uintptr

//go:linkname staticuint64s runtime.staticuint64s
var staticuint64s [256]uint64

type Hasher interface{ Hash() uint64 }

func rtPtr(t reflect.Type) unsafe.Pointer { return (*[2]unsafe.Pointer)(unsafe.Pointer(&t))[1] }

func main() {
	n, _ := strconv.Atoi(os.Args[2])
	switch os.Args[1] {
	case "tanil":
		inter := rtPtr(reflect.TypeOf((*Hasher)(nil)).Elem())
		d := &taDesc{Cache: unsafe.Pointer(&emptyTypeAssertCache[0]), Inter: inter, CanFail: true}
		panics, nonnil := 0, 0
		for i := 0; i < n; i++ {
			func() {
				defer func() {
					if recover() != nil {
						panics++
					}
				}()
				if typeAssert(d, nil) != nil {
					nonnil++
				}
			}()
		}
		fmt.Printf("TANIL calls=%d panicked=%d nonnil=%d\n", n, panics, nonnil)
	case "convt":
		seen := map[uintptr]bool{}
		keep := make([]unsafe.Pointer, 0, n)
		lo := uintptr(unsafe.Pointer(&staticuint64s[0]))
		hi := lo + unsafe.Sizeof(staticuint64s)
		static := 0
		for v := uint64(0); v < 256; v++ {
			if p := uintptr(convT64(v)); p >= lo && p < hi {
				static++
			}
		}
		for i := 0; i < n; i++ {
			p := convT64(uint64(256 + i))
			keep = append(keep, p)
			seen[uintptr(p)] = true
		}
		fmt.Printf("CONVT static=%d/256 fresh=%d/%d\n", static, len(seen), n)
		_ = keep
	}
}
