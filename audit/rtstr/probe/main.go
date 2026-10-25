// Command probertstr exercises the string and slice examples (examples/basic/zstr.go) on the real
// Go 1.26 runtime, so that audit/rtstr/run.sh can check the contracts against it:
//
//	probertstr vectors   capacities the runtime chooses, printed as Lean facts for the specs'
//	                     formulas (growCap for AppendPoint's 24-byte Point, roundupsize for []byte(s))
//	probertstr wb N      N rounds of CopyNodes and AppendPoint-free pointer stores (basic.SetNext)
//	                     with a GC cycle running most of the time, for the gdb probe of HRoom
//	                     (audit/rtstr/wb_amd64.py) at the real gcWriteBarrier calls
//	probertstr strings N N rounds of every string example on random UTF-8-ish inputs, each result
//	                     compared with Go's own builtin (a + b, []byte(s), string(b), for range,
//	                     utf8 rune count, copy)
package main

import (
	"fmt"
	"math/rand"
	"os"
	"runtime"
	"strconv"
	"unicode/utf8"

	"example.com/basic"
)

var nodes []*basic.Node

func main() {
	if len(os.Args) < 2 {
		fmt.Println("usage: probertstr vectors | wb N | strings N")
		os.Exit(2)
	}
	n := 0
	if len(os.Args) > 2 {
		n, _ = strconv.Atoi(os.Args[2])
	}
	switch os.Args[1] {
	case "vectors":
		// growslice for a full []Point of length l (len = cap = l) appending one element
		fmt.Print("example : [")
		first := true
		for l := 0; l <= 1200; l++ {
			s := make([]basic.Point, l)
			t := basic.AppendPoint(s, basic.Point{})
			if !first {
				fmt.Print(", ")
			}
			first = false
			fmt.Printf("(%d, %d)", l, cap(t))
		}
		fmt.Println("].all (fun (l, c) => growCap 24 true (l + 1) l == c) = true := by decide +kernel")
		fmt.Print("example : [")
		first = true
		for k := 0; k <= 3000; k += 7 {
			b := basic.ToBytes(string(make([]byte, k)))
			if !first {
				fmt.Print(", ")
			}
			first = false
			fmt.Printf("(%d, %d)", k, cap(b))
		}
		fmt.Println("].all (fun (k, c) => roundupsize k true == c) = true := by decide +kernel")
	case "wb":
		done := make(chan bool)
		go func() {
			for {
				select {
				case <-done:
					return
				default:
					runtime.GC()
				}
			}
		}()
		for i := 0; i < n; i++ {
			a, b := &basic.Node{}, &basic.Node{}
			basic.SetNext(a, b)
			dst := make([]*basic.Node, 8)
			src := []*basic.Node{a, b, a, b}
			basic.CopyNodes(dst, src)
			nodes = append(nodes[:0], dst...)
		}
		close(done)
		fmt.Println("wb done")
	case "strings":
		r := rand.New(rand.NewSource(1))
		bad := 0
		for i := 0; i < n; i++ {
			mk := func() string {
				b := make([]byte, r.Intn(12))
				for j := range b {
					switch r.Intn(4) {
					case 0:
						b[j] = byte(r.Intn(128))
					default:
						b[j] = byte(128 + r.Intn(128))
					}
				}
				return string(b)
			}
			a, c := mk(), mk()
			if basic.Concat(a, c) != a+c || string(basic.ToBytes(a)) != a || basic.FromBytes([]byte(c)) != c ||
				basic.RuneLen(a) != utf8.RuneCountInString(a) {
				bad++
			}
			var sum uint64
			for _, x := range a {
				sum += uint64(x)
			}
			if basic.SumRunes(a) != sum {
				bad++
			}
			ps := make([]basic.Point, r.Intn(5), 5)
			if got := basic.AppendPoint(ps, basic.Point{X: 1}); len(got) != len(ps)+1 || got[len(ps)].X != 1 {
				bad++
			}
		}
		fmt.Printf("strings rounds=%d mismatches=%d\n", n, bad)
	}
}
