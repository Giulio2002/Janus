package main

import (
	"debug/elf"
	"encoding/binary"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"regexp"
	"sort"

	"github.com/Giulio2002/Janus/oracle/gen"
)

// seqgen writes sequence-mode cases (layout.Case.Words): straight-line blocks laid out from
// TestPC that the runner executes in one go (falling through to the UDF after the last word)
// and the Lean side steps word by word (Oracle/Main.lean runSeq). Two sources:
//
//   - synthetic chains per instruction family (seq/<family>): random blocks over a small
//     register pool, so every instruction reads what an earlier one wrote (the SHA-1/SHA-256/
//     SHA-512/SHA-3/GHASH/CRC32/permute data flow of the real kernels);
//   - windows of real code (seq/harvest): maximal runs of non-branch, non-memory words of the
//     functions of the given arm64 binaries whose symbol matches -syms, cut into random
//     windows of 2-16 words.
func cmdSeqgen(args []string) {
	fs := flag.NewFlagSet("seqgen", flag.ExitOnError)
	n := fs.Int("n", 2000, "synthetic blocks per family")
	k := fs.Int("k", 4, "states per harvested window")
	windows := fs.Int("windows", 4000, "harvested windows (0: none)")
	seed := fs.Uint64("seed", 3, "random seed")
	out := fs.String("o", "seq.jsonl", "output")
	first := fs.Int("first-id", 5_000_000, "first case id")
	syms := fs.String("syms", `^(crypto/|hash/crc32|vendor/golang.org/x/crypto/)`, "regexp: harvest windows from functions whose symbol matches")
	fs.IntVar(&gen.DCZID, "dczid", gen.DCZID, "DCZID_EL0 of the reference machine (runner -dczid)")
	fs.Parse(args)
	r := rand.New(rand.NewPCG(*seed, 0x73657167656e))
	cw := newCaseWriter(*out, *first)
	emit := func(class string, ws []uint32) {
		s := gen.Setup(r, ws[0])
		c := gen.Case(cw.id, class, ws[0], s)
		for _, w := range ws {
			c.Words = append(c.Words, fmt.Sprintf("0x%08x", w))
		}
		cw.enc.Encode(&c)
		cw.id++
		cw.n[class]++
	}
	fams := make([]string, 0, len(seqFamilies))
	for f := range seqFamilies {
		fams = append(fams, f)
	}
	sort.Strings(fams)
	for _, f := range fams {
		g := seqFamilies[f]
		for i := 0; i < *n; i++ {
			emit("seq/"+f, g(r, 2+r.IntN(11)))
		}
	}
	if *windows > 0 && fs.NArg() > 0 {
		re := regexp.MustCompile(*syms)
		var runs [][]uint32
		for _, p := range fs.Args() {
			runs = append(runs, straightRuns(p, re)...)
		}
		if len(runs) > 0 {
			for i := 0; i < *windows; i++ {
				run := runs[r.IntN(len(runs))]
				l := 2 + r.IntN(15)
				if l > len(run) {
					l = len(run)
				}
				off := r.IntN(len(run) - l + 1)
				for j := 0; j < *k; j++ {
					emit("seq/harvest", run[off:off+l])
				}
			}
		}
		fmt.Fprintf(os.Stderr, "seqgen: %d straight-line runs from %d binaries\n", len(runs), fs.NArg())
	}
	cw.close()
}

// straightRuns returns the maximal runs (at least 2 words) of words that are neither
// branches, system instructions nor loads/stores, inside the functions of an arm64 ELF whose
// symbol name matches re. Each distinct run is returned once.
func straightRuns(path string, re *regexp.Regexp) [][]uint32 {
	f, err := elf.Open(path)
	if err != nil {
		die("%s: %v", path, err)
	}
	defer f.Close()
	syms, err := f.Symbols()
	if err != nil {
		die("%s: %v", path, err)
	}
	text := f.Section(".text")
	if text == nil {
		return nil
	}
	data, err := text.Data()
	if err != nil {
		die("%s: %v", path, err)
	}
	seen := map[string]bool{}
	var runs [][]uint32
	for _, s := range syms {
		if elf.ST_TYPE(s.Info) != elf.STT_FUNC || !re.MatchString(s.Name) || s.Size == 0 ||
			s.Value < text.Addr || s.Value+s.Size > text.Addr+text.Size {
			continue
		}
		var cur []uint32
		flush := func() {
			if len(cur) >= 2 {
				key := fmt.Sprint(cur)
				if !seen[key] {
					seen[key] = true
					runs = append(runs, append([]uint32(nil), cur...))
				}
			}
			cur = cur[:0]
		}
		for a := s.Value; a+4 <= s.Value+s.Size; a += 4 {
			w := binary.LittleEndian.Uint32(data[a-text.Addr:])
			c := gen.Classify(w)
			if w == 0 || len(c) < 3 || c[:3] == "br." || c[:3] == "sys" || c == "system" || c == "reserved" ||
				c[:3] == "ls." || c[:4] == "vls." || c == "dpi.pcrel" {
				flush()
				continue
			}
			cur = append(cur, w)
		}
		flush()
	}
	return runs
}

// A family draws a block of `l` words over a small register pool.
type seqFamily func(r *rand.Rand, l int) []uint32

func pool(r *rand.Rand, n int) func() uint32 {
	base := uint32(r.IntN(32 - n + 1))
	return func() uint32 { return base + uint32(r.IntN(n)) }
}

// chain builds a block from word builders (each gets the register pool).
func chain(builders ...func(r *rand.Rand, p func() uint32) uint32) seqFamily {
	return func(r *rand.Rand, l int) []uint32 {
		p := pool(r, 3+r.IntN(4))
		ws := make([]uint32, l)
		for i := range ws {
			ws[i] = builders[r.IntN(len(builders))](r, p)
		}
		return ws
	}
}

// rdm: Rd/Rn/Rm three-register form `base | m<<16 | n<<5 | d`.
func rdm(base uint32) func(r *rand.Rand, p func() uint32) uint32 {
	return func(r *rand.Rand, p func() uint32) uint32 { return base | p()<<16 | p()<<5 | p() }
}

// rdn: two-register form `base | n<<5 | d`.
func rdn(base uint32) func(r *rand.Rand, p func() uint32) uint32 {
	return func(r *rand.Rand, p func() uint32) uint32 { return base | p()<<5 | p() }
}

var seqFamilies = map[string]seqFamily{
	"sha1": chain(rdm(0x5E000000), rdm(0x5E001000), rdm(0x5E002000), rdm(0x5E003000), // SHA1C/P/M/SU0
		rdn(0x5E280800), rdn(0x5E281800), // SHA1H, SHA1SU1
		rdn(0x5E040400),  // DUP S, V.S[0]
		rdm(0x4EA08400)), // ADD .4S
	"sha256": chain(rdm(0x5E004000), rdm(0x5E005000), rdm(0x5E006000), rdn(0x5E282800), // SHA256H/H2/SU1/SU0
		rdm(0x4EA08400), rdm(0x4EA01C00)), // ADD .4S, ORR .16B
	"sha512": chain(rdm(0xCE608000), rdm(0xCE608400), rdm(0xCE608800), rdn(0xCEC08000), // SHA512H/H2/SU1/SU0
		rdm(0x6E004000), rdm(0x4EE08400)), // EXT #8 .16B, ADD .2D
	"sha3": chain(
		func(r *rand.Rand, p func() uint32) uint32 { // EOR3 / BCAX
			return 0xCE000000 | u1(r)<<21 | p()<<16 | p()<<10 | p()<<5 | p()
		},
		rdm(0xCE608C00), // RAX1
		func(r *rand.Rand, p func() uint32) uint32 { // XAR
			return 0xCE800000 | p()<<16 | uint32(r.IntN(64))<<10 | p()<<5 | p()
		},
		rdm(0x6E201C00)), // EOR .16B
	"ghash": chain(rdm(0x0EE0E000), rdm(0x4EE0E000), rdm(0x0E20E000), rdm(0x4E20E000), // PMULL{2} 1Q / 8H
		rdm(0x6E004000), rdm(0x6E201C00), // EXT #8, EOR
		rdn(0x4E284800), rdn(0x4E286800)), // AESE, AESMC
	"crc32": func(r *rand.Rand, l int) []uint32 {
		p := pool(r, 3+r.IntN(3))
		if r.IntN(2) == 0 {
			p = func() uint32 { return uint32(r.IntN(31)) }
		}
		acc := p()
		ws := make([]uint32, l)
		for i := range ws {
			sz := uint32(r.IntN(4))
			sf := uint32(0)
			if sz == 3 {
				sf = 1
			}
			d, n := acc, acc
			if r.IntN(5) == 0 {
				d, n = p(), p()
			}
			ws[i] = 0x1AC04000 | sf<<31 | p()<<16 | u1(r)<<12 | sz<<10 | n<<5 | d
		}
		return ws
	},
	"permute": chain(
		func(r *rand.Rand, p func() uint32) uint32 { // ZIP/UZP/TRN, every size
			q, size := u1(r), uint32(r.IntN(4))
			if size == 3 {
				q = 1
			}
			opc := []uint32{1, 2, 3, 5, 6, 7}[r.IntN(6)]
			return 0x0E000800 | q<<30 | size<<22 | p()<<16 | opc<<12 | p()<<5 | p()
		},
		rdm(0x4E000000), // TBL .16B (one register)
		rdn(0x6E200800), // REV32 .16B
		func(r *rand.Rand, p func() uint32) uint32 { // DUP (element, scalar)
			imm5 := uint32(1 + r.IntN(31))
			if imm5&0xf == 0 {
				imm5 |= 2
			}
			return 0x5E000400 | imm5<<16 | p()<<5 | p()
		}),
}

func u1(r *rand.Rand) uint32 { return uint32(r.IntN(2)) }
