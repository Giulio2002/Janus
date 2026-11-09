package main

// The in-process MCacheOK probe (arm64; `probe9 mcache N`, run under qemu-aarch64). Just before
// each of N string concatenations of 64 bytes (runtime.concatstring2 → rawstring →
// mallocgc(64, nil, false): a pointer-free request MallocFast covers), it reads the runtime
// state MallocFast's precondition MCacheOK talks about, at the offsets the proof uses (Go 1.26
// linux/arm64), without allocating, and counts which conjuncts fail. The runtime globals'
// addresses come from the binary's own symbol table.

import (
	"debug/elf"
	"fmt"
	"os"
	"strings"
	"unsafe"
)

func getg() uintptr

func rd(a uintptr, n int) uint64 {
	var v uint64
	for i := n - 1; i >= 0; i-- {
		v = v<<8 | uint64(*(*byte)(unsafe.Pointer(a + uintptr(i))))
	}
	return v
}

type glob struct{ a, n uintptr }

func apart(a, n, b, k uintptr) bool { return a+n <= b || b+k <= a }

var condNames = []string{"p != 0", "sc < 68", "allocCache != 0", "res < nelems", "refill cond",
	"slot != 0", "span.needzero = 0", "slot zero", "elemsize = class size", "debug.malloc off",
	"gcBlackenEnabled = 0", "writeBarrier off", "no sample due", "MemProfileRate = c.memProfRate",
	"Spread (runtime objects)", "apart from one globals range [globLo, globHi) (shipped MCacheOK)",
	"apart from each global (round 9 MCacheOK)", "m is runtime.m0"}

func mcacheProbe(n int) {
	f, err := elf.Open("/proc/self/exe")
	if err != nil {
		panic(err)
	}
	syms, _ := f.Symbols()
	S := map[string]uintptr{}
	for _, s := range syms {
		S[s.Name] = uintptr(s.Value)
	}
	G := []glob{{S["runtime.debug"] + 0x2c, 1}, {S["runtime.gcBlackenEnabled"], 4},
		{S["internal/runtime/gc.SizeToSizeClass8"], 129}, {S["internal/runtime/gc.SizeClassToSize"], 136},
		{S["runtime.writeBarrier"], 1}, {S["runtime.MemProfileRate"], 8}}
	lo, hi := G[0].a, G[0].a+G[0].n
	for _, g := range G {
		lo, hi = min(lo, g.a), max(hi, g.a+g.n)
	}
	m0 := S["runtime.m0"]
	fail := make([]int, len(condNames))
	var shipped, fixed int
	conds := make([]bool, len(condNames))
	a, b := strings.Repeat("a", 32), strings.Repeat("b", 32)
	const size = 64
	for it := 0; it < n; it++ {
		var sp uintptr
		sp = uintptr(unsafe.Pointer(&sp)) // a stack address (the call's SP is close below)
		g := getg()
		m := uintptr(rd(g+48, 8))
		p := uintptr(rd(m+208, 8))
		for i := range conds {
			conds[i] = true
		}
		conds[0] = p != 0
		if p != 0 {
			c := uintptr(rd(p+56, 8))
			sc := uintptr(rd(G[2].a+(size+7)/8, 1))
			cs := uintptr(rd(G[3].a+2*sc, 2))
			span := uintptr(rd(c+48+8*(2*sc+1), 8))
			cache := rd(span+56, 8)
			fidx := uintptr(rd(span+48, 2))
			nel := uintptr(rd(span+50, 2))
			base := uintptr(rd(span+24, 8))
			esz := uintptr(rd(span+104, 8))
			nz := rd(span+100, 1)
			ctz := uintptr(64)
			for i := uintptr(0); i < 64; i++ {
				if cache>>i&1 == 1 {
					ctz = i
					break
				}
			}
			res := ctz + fidx
			slot := base + esz*res
			zero := slot != 0 && res < nel
			if zero {
				for i := uintptr(0); i < cs; i++ {
					if *(*byte)(unsafe.Pointer(slot + i)) != 0 {
						zero = false
						break
					}
				}
			}
			conds[1] = sc < 68
			conds[2] = cache != 0
			conds[3] = res < nel
			conds[4] = (res+1)%64 != 0 || res+1 == nel
			conds[5] = slot != 0
			conds[6] = nz == 0
			conds[7] = zero
			conds[8] = esz == cs
			conds[9] = rd(G[0].a, 1)%2 == 0
			conds[10] = rd(G[1].a, 4) == 0
			conds[11] = rd(G[4].a, 1)%2 == 0
			conds[12] = (rd(c, 8)-uint64(cs))>>63 == 0
			conds[13] = rd(G[5].a, 8) == rd(c+8, 8)
			objs := []glob{{sp - 4096, 4096 + 184}, {g + 16, 162}, {m + 208, 60}, {p + 56, 8}, {c, 1136},
				{span + 24, 88}, {slot, cs}}
			for i := range objs {
				for j := 0; j < i; j++ {
					if !apart(objs[i].a, objs[i].n, objs[j].a, objs[j].n) {
						conds[14] = false
					}
				}
				if !apart(objs[i].a, objs[i].n, lo, hi-lo) {
					conds[15] = false
				}
				for _, gl := range G {
					if !apart(objs[i].a, objs[i].n, gl.a, gl.n) {
						conds[16] = false
					}
				}
			}
		}
		conds[17] = m != m0
		okShipped, okFixed := true, true
		for i, v := range conds {
			if !v {
				fail[i]++
				if i != 16 && i != 17 {
					okShipped = false
				}
				if i != 15 && i != 17 {
					okFixed = false
				}
			}
		}
		if okShipped {
			shipped++
		}
		if okFixed {
			fixed++
		}
		strSink = a + b
	}
	fmt.Printf("PROBE mcache-arm64: calls=%d MCacheOK(shipped)=%d MCacheOK(round 9)=%d\n", n, shipped, fixed)
	for i, c := range fail {
		if c > 0 {
			name := condNames[i]
			if i == 17 {
				name = "m is not runtime.m0"
			}
			fmt.Printf("  failed %-70s %d/%d\n", name, c, n)
		}
	}
	os.Stdout.Sync()
}
