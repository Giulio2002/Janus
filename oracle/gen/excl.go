package gen

import (
	"fmt"
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

// Exclusive-monitor sequences (class seq.excl): short blocks of load-exclusive /
// store-exclusive pairs and the instructions that interact with the monitor (CLREX, plain
// stores, a second load-exclusive, a second store-exclusive), run in the sequence mode of the
// native runner (Case.Words: the block is laid out from TestPC and runs until it falls through
// to the UDF after it). The runner executes CLREX before every case, so the monitor starts in
// the Open Access state; the Lean side (janus-oracle) runs every case under every outcome stream
// of the store-exclusives and the comparator accepts any of the model's outcomes
// (docs/ORACLE.md, "Nondeterministic outcomes").

func encLdxr(size, o0, rn, rt uint32) uint32 {
	return 0x08400000 | size<<30 | 31<<16 | o0<<15 | 31<<10 | rn<<5 | rt
}

func encStxr(size, o0, rs, rn, rt uint32) uint32 {
	return 0x08000000 | size<<30 | rs<<16 | o0<<15 | 31<<10 | rn<<5 | rt
}

// sz: 0 = 32-bit registers, 1 = 64-bit registers.
func encLdxp(sz, o0, rt2, rn, rt uint32) uint32 {
	return 0x88600000 | sz<<30 | 31<<16 | o0<<15 | rt2<<10 | rn<<5 | rt
}

func encStxp(sz, o0, rs, rt2, rn, rt uint32) uint32 {
	return 0x88200000 | sz<<30 | rs<<16 | o0<<15 | rt2<<10 | rn<<5 | rt
}

const encClrex = 0xD503305F

func encAddImm(rd, rn, imm uint32) uint32 { return 0x91000000 | (imm&0xfff)<<10 | rn<<5 | rd }

// encStr: STR{B,H,W,X} Rt, [Xn] (unsigned offset 0).
func encStr(size, rn, rt uint32) uint32 { return 0x39000000 | size<<30 | rn<<5 | rt }

// encCbnz: CBNZ Wt, #4*off (off in words, may be negative).
func encCbnz(rt uint32, off int) uint32 { return 0x35000000 | (uint32(off)&0x7ffff)<<5 | rt }

// distinct draws n distinct registers from X0..X30 that avoid the ones in `not`.
func distinct(r *rand.Rand, n int, not ...uint32) []uint32 {
	used := map[uint32]bool{}
	for _, x := range not {
		used[x] = true
	}
	var out []uint32
	for len(out) < n {
		x := uint32(r.IntN(31))
		if !used[x] {
			used[x] = true
			out = append(out, x)
		}
	}
	return out
}

// exclEA picks a base address for an exclusive access of `size` bytes: mostly aligned inside
// the buffer, sometimes misaligned (alignment fault) or outside it.
func exclEA(r *rand.Rand, size uint64) uint64 {
	switch p := r.IntN(100); {
	case p < 88:
		return (L.DataBase + 64 + uint64(r.IntN(L.DataSize-128))) &^ 15 &^ (size - 1)
	case p < 94:
		return (L.DataBase + 64 + uint64(r.IntN(L.DataSize-128))) | 1
	default:
		return L.DataBase + L.DataSize + uint64(r.IntN(64))
	}
}

// ExclSeq draws one exclusive-monitor block and its initial state.
func ExclSeq(r *rand.Rand) ([]uint32, State) {
	var s State
	for i := range s.X {
		s.X[i] = Value(r)
	}
	s.SP = (L.DataBase + 2048) &^ 15
	s.NZCV = r.IntN(16)
	s.Seed = r.Uint64() & 0xffffffff
	setupV(r, &s)
	size := uint32(r.IntN(4))
	o0 := func() uint32 { return uint32(r.IntN(2)) }
	rg := distinct(r, 6)
	bA, bB, t1, t2, st, st2 := rg[0], rg[1], rg[2], rg[3], rg[4], rg[5]
	eaA := exclEA(r, 1<<size)
	s.X[bA] = eaA
	// bB: the same address, a neighbour in the same 16 bytes (maybe the same reservation
	// granule), or another place in the buffer.
	switch r.IntN(3) {
	case 0:
		s.X[bB] = eaA
	case 1:
		s.X[bB] = eaA + 16 + uint64(r.IntN(4))*16
	default:
		s.X[bB] = exclEA(r, 1<<size)
	}
	k := uint32(r.IntN(4096))
	var w []uint32
	switch r.IntN(13) {
	case 0, 1: // the LL/SC read-modify-write, same address and size
		w = []uint32{encLdxr(size, o0(), bA, t1), encAddImm(t2, t1, k), encStxr(size, o0(), st, bA, t2)}
	case 2: // the Go retry loop: LDAXR; ADD; STLXR; CBNZ back to LDAXR
		w = []uint32{encLdxr(size, 1, bA, t1), encAddImm(t2, t1, k), encStxr(size, 1, st, bA, t2), encCbnz(st, -3)}
	case 3: // another address
		w = []uint32{encLdxr(size, o0(), bA, t1), encStxr(size, o0(), st, bB, t2)}
	case 4: // another size, same address
		size2 := uint32(r.IntN(4))
		w = []uint32{encLdxr(size, o0(), bA, t1), encStxr(size2, o0(), st, bA, t2)}
	case 5: // CLREX in between: must fail
		w = []uint32{encLdxr(size, o0(), bA, t1), encClrex, encStxr(size, o0(), st, bA, t2)}
	case 6: // two store-exclusives after one load-exclusive: the second must fail
		w = []uint32{encLdxr(size, o0(), bA, t1), encStxr(size, o0(), st, bA, t2), encStxr(size, o0(), st2, bA, t1)}
	case 7: // no load-exclusive (monitor open): must fail; then a pair
		w = []uint32{encStxr(size, o0(), st, bA, t2), encLdxr(size, o0(), bA, t1), encStxr(size, o0(), st2, bA, t2)}
	case 8: // a plain store to the marked bytes (or next to them) in between
		b := bA
		if r.IntN(2) == 0 {
			b = bB
		}
		w = []uint32{encLdxr(size, o0(), bA, t1), encStr(uint32(r.IntN(4)), b, t2), encStxr(size, o0(), st, bA, t2)}
	case 9: // re-marking: the second load-exclusive replaces the first mark
		w = []uint32{encLdxr(size, o0(), bA, t1), encLdxr(size, o0(), bB, t2), encStxr(size, o0(), st, bA, t2),
			encStxr(size, o0(), st2, bB, t1)}
	case 10, 11: // exclusive pairs (LDXP/STXP), 32- or 64-bit registers
		sz := uint32(r.IntN(2))
		s.X[bA] = exclEA(r, 8<<sz)
		t3 := distinct(r, 1, rg...)[0]
		if r.IntN(2) == 0 {
			w = []uint32{encLdxp(sz, o0(), t2, bA, t1), encAddImm(t3, t1, k), encStxp(sz, o0(), st, t2, bA, t3)}
		} else { // mismatches: a single-register store-exclusive, or another address
			if r.IntN(2) == 0 {
				w = []uint32{encLdxp(sz, o0(), t2, bA, t1), encStxr(2+sz, o0(), st, bA, t3)}
			} else {
				w = []uint32{encLdxr(2+sz, o0(), bA, t1), encStxp(sz, o0(), st, t2, bB, t3)}
			}
		}
	default: // random mix of the above building blocks (up to 6 words)
		n := 2 + r.IntN(5)
		bases := []uint32{bA, bB}
		for i := 0; i < n; i++ {
			b := bases[r.IntN(2)]
			sz := uint32(r.IntN(4))
			switch r.IntN(6) {
			case 0, 1:
				w = append(w, encLdxr(sz, o0(), b, t1))
			case 2, 3:
				w = append(w, encStxr(sz, o0(), pick(r, st, st2), b, t2))
			case 4:
				w = append(w, encClrex)
			default:
				w = append(w, encStr(sz, b, t2))
			}
		}
	}
	// Sometimes SP is the first base: CheckSPAlignment (SP is 16-aligned here), then the access.
	if r.IntN(10) == 0 && s.X[bA]%16 == 0 {
		s.SP = s.X[bA]
		for i, x := range w {
			if (x&0x3F000000 == 0x08000000 || x&0x3FC00000 == 0x39000000) && (x>>5)&31 == bA {
				w[i] = x | 31<<5
			}
		}
	}
	return w, s
}

// isLdExcl / isStExcl: LDXR/LDAXR and STXR/STLXR (any size; not the pairs).
func isLdExcl(w uint32) bool { return w&0x3FE08000 == 0x08400000 || w&0x3FE08000 == 0x08408000 }
func isStExcl(w uint32) bool { return w&0x3FE00000 == 0x08000000 }

// plainDP: data processing (immediate or register) that neither branches nor touches memory.
func plainDP(w uint32) bool {
	op0 := (w >> 25) & 0xf
	return op0&0xe == 0x8 || op0&0x7 == 0x5 // 100x: DP immediate; x101: DP register
}

// ExclLoops finds the LL/SC retry loops of real code in a stream of words: a load-exclusive,
// plain data processing, a store-exclusive to the same base register, and CBNZ on its status
// back to the load-exclusive. Each is returned once (the words from the load to the CBNZ).
func ExclLoops(ws []uint32) [][]uint32 {
	var out [][]uint32
	seen := map[string]bool{}
	for i, w := range ws {
		if !isLdExcl(w) {
			continue
		}
		rn := (w >> 5) & 31
		for j := i + 1; j < len(ws) && j < i+8; j++ {
			x := ws[j]
			if plainDP(x) {
				continue
			}
			if !isStExcl(x) || (x>>5)&31 != rn || j+1 >= len(ws) {
				break
			}
			cb := ws[j+1]
			st := (x >> 16) & 31
			off := int32(cb<<8) >> 13 // imm19, sign-extended
			if cb&0x7F000000 == 0x35000000 && cb&31 == st && int(off) == i-(j+1) {
				loop := append([]uint32(nil), ws[i:j+2]...)
				k := fmt.Sprint(loop)
				if !seen[k] {
					seen[k] = true
					out = append(out, loop)
				}
			}
			break
		}
	}
	return out
}

// LoopState: a random state whose base register (the load-exclusive's Rn) points at an aligned
// word of the buffer (or SP, when Rn is 31).
func LoopState(r *rand.Rand, loop []uint32) State {
	var s State
	for i := range s.X {
		s.X[i] = Value(r)
	}
	s.NZCV = r.IntN(16)
	s.Seed = r.Uint64() & 0xffffffff
	setupV(r, &s)
	ea := (L.DataBase + 64 + uint64(r.IntN(L.DataSize-128))) &^ 15
	s.SP = (L.DataBase + 2048) &^ 15
	if rn := (loop[0] >> 5) & 31; rn == 31 {
		s.SP = ea
	} else {
		s.X[rn] = ea
	}
	return s
}
