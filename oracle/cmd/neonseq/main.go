// Command neonseq writes sequence-mode oracle cases for the Advanced SIMD model: straight-line
// blocks of 4-24 instructions (`Case.Words`, laid out from TestPC by the runner; the Lean side
// threads the state through `Oracle.Main.runSeq`) drawn from the targeted NEON generators, the
// SIMD&FP loads and stores (based on X20-X23, which point into the data buffer) and the
// scalar FP data-processing classes. Registers come from a small pool (V0-V7 most of the
// time) so instructions consume each other's results, which tests the composition of steps,
// the zeroing of upper halves and FPSR accumulation across instructions.
//
// Only words that the trusted decoder accepts are used (`-decode janus-decode`), so a block is
// never cut short by an undecodable word.
//
//	neonseq -n 20000 -seed 1 -decode .lake/build/bin/janus-decode -o seq.jsonl
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"os/exec"
	"sort"
	"strings"

	"github.com/Giulio2002/Janus/oracle/gen"
	L "github.com/Giulio2002/Janus/oracle/layout"
)

func bits(w uint32, hi, lo int) uint32 { return (w >> lo) & (1<<(hi-lo+1) - 1) }

// pool rewrites the register fields of a data-processing word to the small pool V0-V7
// (Rd, Rn, Rm; for the by-element classes Rm is 4 bits).
func pool(r *rand.Rand, w uint32) uint32 {
	p := func() uint32 { return uint32(r.IntN(8)) }
	w = w&^0x3FF | p()<<5 | p()
	cls := gen.Classify(w)
	switch cls {
	case "simd.elem", "simd.selem":
		w = w&^(0x1F<<16) | p()<<16
	case "simd.3same", "simd.s3same", "simd.3diff", "simd.s3diff", "simd.perm", "simd.ext",
		"simd.tbl", "fp.dp2", "fp.dp3", "fp.csel", "fp.ccmp", "fp.cmp":
		w = w&^(0x1F<<16) | p()<<16
	}
	if cls == "fp.dp3" {
		w = w&^(0x1F<<10) | p()<<10
	}
	return w
}

// memWord draws a SIMD&FP load/store based on X20-X23 with a small offset (so it lands in the
// buffer) and a pool transfer register.
func memWord(r *rand.Rand) uint32 {
	base := uint32(20 + r.IntN(4))
	rt := uint32(r.IntN(8))
	switch r.IntN(6) {
	case 0: // LDR/STR Q/D/S unsigned offset
		sz := []uint32{0b10 << 30, 0b11 << 30, 0b00<<30 | 1<<23}[r.IntN(3)]
		return 0x3D000000 | sz | uint32(r.IntN(2))<<22 | uint32(r.IntN(32))<<10 | base<<5 | rt
	case 1: // LD1/ST1 multiple, no offset
		op := []uint32{0b0111, 0b1010, 0b0110, 0b0010}[r.IntN(4)]
		return 0x0C000000 | uint32(r.IntN(2))<<30 | uint32(r.IntN(2))<<22 | op<<12 | uint32(r.IntN(4))<<10 | base<<5 | rt
	case 2, 3: // LD2-LD4/ST2-ST4, sometimes post-index by the transfer size
		op := []uint32{0b0000, 0b0100, 0b1000}[r.IntN(3)]
		w := 0x0C000000 | uint32(r.IntN(2))<<30 | uint32(r.IntN(2))<<22 | op<<12 | uint32(r.IntN(4))<<10 | base<<5 | rt
		if r.IntN(3) == 0 {
			w |= 1<<23 | 31<<16
		}
		return w
	case 4: // LDP/STP/LDNP/STNP of Q/D/S
		opc := uint32(r.IntN(3))
		idx := []uint32{0, 2}[r.IntN(2)]
		rt2 := uint32(r.IntN(8))
		if rt2 == rt {
			rt2 = (rt + 1) % 8
		}
		return 0x2C000000 | opc<<30 | idx<<23 | uint32(r.IntN(2))<<22 | uint32(r.IntN(8))<<15 | rt2<<10 | base<<5 | rt
	}
	// LD1R / LD1 single structure
	return 0x0D40C000 | uint32(r.IntN(2))<<30 | uint32(r.IntN(4))<<10 | base<<5 | rt
}

func main() {
	n := flag.Int("n", 10000, "cases")
	seed := flag.Uint64("seed", 1, "random seed")
	out := flag.String("o", "seq.jsonl", "output")
	decode := flag.String("decode", ".lake/build/bin/janus-decode", "janus-decode executable")
	dczid := flag.Int("dczid", 7, "DCZID_EL0 of the reference")
	first := flag.Int("first-id", 50_000_000, "first case id")
	flag.Parse()
	r := rand.New(rand.NewPCG(*seed, 0x6e656f6e))

	var dp []string
	for k := range gen.Targeted {
		if strings.HasPrefix(k, "neon.") || strings.HasPrefix(k, "simd.") || strings.HasPrefix(k, "fp.") {
			dp = append(dp, k)
		}
	}
	sort.Strings(dp)

	// Draw candidate words, then keep the ones the decoder accepts.
	const per = 64
	cand := make([]uint32, 0, *n*per)
	for len(cand) < *n*per {
		if r.IntN(5) == 0 {
			cand = append(cand, memWord(r))
		} else {
			w := gen.Targeted[dp[r.IntN(len(dp))]](r)
			if c := gen.Classify(w); !strings.HasPrefix(c, "simd.") && !strings.HasPrefix(c, "fp.") {
				continue
			}
			if gen.Classify(w) == "simd.copy" || gen.Classify(w) == "simd.fmovgen" ||
				gen.Classify(w) == "fp.cvtint" || gen.Classify(w) == "fp.cvtfix" {
				continue // general-register destinations would leave the pool; keep them in single-step
			}
			cand = append(cand, pool(r, w))
		}
	}
	ok := decodable(*decode, cand)
	var words []uint32
	for _, w := range cand {
		if ok[w] {
			words = append(words, w)
		}
	}
	fmt.Fprintf(os.Stderr, "neonseq: %d candidate words, %d decodable\n", len(cand), len(words))

	f, err := os.Create(*out)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	bw := bufio.NewWriter(f)
	enc := json.NewEncoder(bw)
	for i := 0; i < *n; i++ {
		k := 4 + r.IntN(21)
		ws := make([]string, k)
		for j := range ws {
			ws[j] = fmt.Sprintf("0x%08x", words[r.IntN(len(words))])
		}
		// a state drawn for one of the block's words (FP edge lanes, saturation lanes, ...)
		w0 := uint32(0)
		fmt.Sscanf(ws[r.IntN(k)], "0x%x", &w0)
		s := gen.Setup(r, w0)
		for b := 20; b < 24; b++ {
			s.X[b] = L.DataBase + 512 + uint64(r.IntN(L.DataSize-1536))&^15
		}
		s.SP = L.DataBase + 16*uint64(16+r.IntN(224))
		c := gen.Case(*first+i, "seq/neon", 0, s)
		c.Word = "0x00000000"
		c.DCZID = *dczid
		c.Words = ws
		enc.Encode(&c)
	}
	bw.Flush()
	f.Close()
}

// decodable runs the trusted decoder over the distinct words and returns the accepted set.
func decodable(exe string, ws []uint32) map[uint32]bool {
	seen := map[uint32]bool{}
	var in strings.Builder
	for _, w := range ws {
		if !seen[w] {
			seen[w] = true
			fmt.Fprintf(&in, "0x%08x\n", w)
		}
	}
	cmd := exec.Command(exe)
	cmd.Stdin = strings.NewReader(in.String())
	outb, err := cmd.Output()
	if err != nil {
		fmt.Fprintln(os.Stderr, "decode:", err)
		os.Exit(1)
	}
	ok := map[uint32]bool{}
	for _, line := range strings.Split(string(outb), "\n") {
		f := strings.Fields(line)
		if len(f) >= 2 && f[1] == "ok" {
			var w uint32
			fmt.Sscanf(f[0], "0x%x", &w)
			ok[w] = true
		}
	}
	return ok
}
