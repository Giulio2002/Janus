// Command oracle generates differential test cases for the Janus AArch64 model, runs them
// natively (cmd/runner under qemu-aarch64) and through `janus-oracle` (Janus.Arm64.step),
// and compares the two. See docs/ORACLE.md.
//
//	oracle gen     -n 2000 -seed 1 -o gen.jsonl            randomised encodings per class
//	oracle harvest -k 2 -o harvest.jsonl BIN...            every distinct word in .text of BINs
//	oracle run     -cases a.jsonl,b.jsonl -out DIR         run both sides, compare, report
//	oracle report  -out DIR                                re-render DIR/summary.md
//	oracle minimize -out DIR                               shrink mismatching cases to repro.md
//	oracle selftest                                        check the native harness itself
package main

import (
	"bufio"
	"debug/elf"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"sort"
	"strings"

	"github.com/Giulio2002/Janus/oracle/gen"
	L "github.com/Giulio2002/Janus/oracle/layout"
)

func die(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "oracle: "+f+"\n", a...)
	os.Exit(1)
}

func main() {
	if len(os.Args) < 2 {
		die("usage: oracle gen|harvest|run|report|minimize|selftest [flags]")
	}
	switch os.Args[1] {
	case "gen":
		cmdGen(os.Args[2:])
	case "harvest":
		cmdHarvest(os.Args[2:])
	case "run":
		cmdRun(os.Args[2:])
	case "report":
		cmdReport(os.Args[2:])
	case "selftest":
		cmdSelftest(os.Args[2:])
	case "minimize":
		cmdMinimize(os.Args[2:])
	default:
		die("unknown command %q", os.Args[1])
	}
}

type caseWriter struct {
	w   *bufio.Writer
	enc *json.Encoder
	f   *os.File
	id  int
	n   map[string]int
}

func newCaseWriter(path string, firstID int) *caseWriter {
	f, err := os.Create(path)
	if err != nil {
		die("%v", err)
	}
	w := bufio.NewWriter(f)
	return &caseWriter{w: w, enc: json.NewEncoder(w), f: f, id: firstID, n: map[string]int{}}
}

func (cw *caseWriter) add(r *rand.Rand, class string, w uint32, k int) {
	for j := 0; j < k; j++ {
		s := gen.Setup(r, w)
		if gen.Conditional(gen.Classify(w)) {
			for f := 0; f < 16; f++ {
				s.NZCV = f
				c := gen.Case(cw.id, class, w, s)
				cw.enc.Encode(&c)
				cw.id++
				cw.n[class]++
			}
			continue
		}
		c := gen.Case(cw.id, class, w, s)
		cw.enc.Encode(&c)
		cw.id++
		cw.n[class]++
	}
}

func (cw *caseWriter) close() {
	cw.w.Flush()
	cw.f.Close()
	total := 0
	keys := make([]string, 0, len(cw.n))
	for k, v := range cw.n {
		keys = append(keys, k)
		total += v
	}
	sort.Strings(keys)
	for _, k := range keys {
		fmt.Fprintf(os.Stderr, "  %-28s %7d cases\n", k, cw.n[k])
	}
	fmt.Fprintf(os.Stderr, "  %-28s %7d cases\n", "total", total)
}

func cmdGen(args []string) {
	fs := flag.NewFlagSet("gen", flag.ExitOnError)
	n := fs.Int("n", 2000, "words per targeted class (conditional classes run each word under all 16 NZCV)")
	ng := fs.Int("group", 3000, "fully random words per top-level encoding group")
	seed := fs.Uint64("seed", 1, "random seed")
	out := fs.String("o", "gen.jsonl", "output")
	first := fs.Int("first-id", 1_000_000, "first case id")
	fs.Parse(args)
	r := rand.New(rand.NewPCG(*seed, 0x6a616e7573))
	cw := newCaseWriter(*out, *first)
	names := make([]string, 0, len(gen.Targeted))
	for k := range gen.Targeted {
		names = append(names, k)
	}
	sort.Strings(names)
	for _, name := range names {
		g := gen.Targeted[name]
		nw := *n
		if gen.Conditional(name) {
			nw = (*n + 7) / 8
		}
		for i := 0; i < nw; i++ {
			w := g(r)
			for gen.Unpredictable(w) || !gen.Tested(gen.Classify(w)) {
				w = g(r)
			}
			cw.add(r, "gen/"+gen.Classify(w), w, 1)
		}
	}
	groups := []string{"br", "dpi", "dpr", "ls"}
	for _, name := range groups {
		for i := 0; i < *ng; i++ {
			w := gen.Groups[name](r)
			for gen.Unpredictable(w) || !gen.Tested(gen.Classify(w)) {
				w = gen.Groups[name](r)
			}
			cls := gen.Classify(w)
			k := 1
			if gen.Conditional(cls) {
				k = 0 // one word, 16 flag combinations would swamp the group; use 1 random state
				s := gen.Setup(r, w)
				c := gen.Case(cw.id, "rand/"+cls, w, s)
				cw.enc.Encode(&c)
				cw.id++
				cw.n["rand/"+cls]++
			}
			if k > 0 {
				cw.add(r, "rand/"+cls, w, k)
			}
		}
	}
	cw.close()
}

// textWords returns every 32-bit word of the executable sections of an ELF file.
func textWords(path string) []uint32 {
	f, err := elf.Open(path)
	if err != nil {
		die("%s: %v", path, err)
	}
	defer f.Close()
	if f.Machine != elf.EM_AARCH64 {
		die("%s: not an arm64 ELF", path)
	}
	var ws []uint32
	for _, s := range f.Sections {
		if s.Type != elf.SHT_PROGBITS || s.Flags&elf.SHF_EXECINSTR == 0 {
			continue
		}
		b, err := s.Data()
		if err != nil {
			die("%s: %v", path, err)
		}
		for i := 0; i+4 <= len(b); i += 4 {
			ws = append(ws, binary.LittleEndian.Uint32(b[i:]))
		}
	}
	return ws
}

func cmdHarvest(args []string) {
	fs := flag.NewFlagSet("harvest", flag.ExitOnError)
	k := fs.Int("k", 2, "random states per harvested word")
	seed := fs.Uint64("seed", 2, "random seed")
	out := fs.String("o", "harvest.jsonl", "output")
	perClass := fs.Int("per-class", 6000, "keep at most this many distinct words per class (0 = all), sampled uniformly")
	first := fs.Int("first-id", 1, "first case id")
	fs.Parse(args)
	seen := map[uint32]bool{}
	var words []uint32
	total, skipped := 0, map[string]int{}
	for _, p := range fs.Args() {
		for _, w := range textWords(p) {
			total++
			if seen[w] {
				continue
			}
			seen[w] = true
			cls := gen.Classify(w)
			if !gen.Tested(cls) {
				skipped[cls]++
				continue
			}
			words = append(words, w)
		}
	}
	fmt.Fprintf(os.Stderr, "harvest: %d words, %d distinct, %d in scope (skipped: %v)\n", total, len(seen), len(words), skipped)
	r := rand.New(rand.NewPCG(*seed, 0x6861727665))
	if *perClass > 0 {
		r.Shuffle(len(words), func(i, j int) { words[i], words[j] = words[j], words[i] })
		kept, n := words[:0], map[string]int{}
		for _, w := range words {
			if c := gen.Classify(w); n[c] < *perClass {
				n[c]++
				kept = append(kept, w)
			}
		}
		words = kept
	}
	sort.Slice(words, func(i, j int) bool { return words[i] < words[j] })
	cw := newCaseWriter(*out, *first)
	for _, w := range words {
		cls := "harvest/" + gen.Classify(w)
		if gen.Unpredictable(w) {
			cls += "!unpredictable"
		}
		kk := *k
		if gen.Conditional(gen.Classify(w)) {
			kk = 1
		}
		cw.add(r, cls, w, kk)
	}
	cw.close()
}

func readJSONL[T any](path string) []T {
	f, err := os.Open(path)
	if err != nil {
		die("%v", err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	var out []T
	for sc.Scan() {
		if len(strings.TrimSpace(sc.Text())) == 0 {
			continue
		}
		var v T
		if err := json.Unmarshal(sc.Bytes(), &v); err != nil {
			die("%s: %v", path, err)
		}
		out = append(out, v)
	}
	return out
}

func writeJSONL[T any](path string, xs []T) {
	f, err := os.Create(path)
	if err != nil {
		die("%v", err)
	}
	w := bufio.NewWriter(f)
	enc := json.NewEncoder(w)
	for i := range xs {
		enc.Encode(&xs[i])
	}
	w.Flush()
	f.Close()
}

var _ = L.TestPC
