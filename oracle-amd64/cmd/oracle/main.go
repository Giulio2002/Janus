// Command oracle generates differential test cases for the Janus x86-64 model, runs them
// natively (cmd/runner, single-stepped on the host CPU) and through `janus-oracle-amd64`
// (Janus.Amd64.step), and compares the two. See docs/ORACLE-AMD64.md.
//
//	oracle gen      -n 600 -group 40000 -seed 1 -o gen.jsonl   targeted + random encodings
//	oracle harvest  -k 3 -o harvest.jsonl BIN...               distinct instructions of Go amd64 ELFs
//	oracle run      -cases a.jsonl,b.jsonl -out DIR            run both sides, compare, report
//	oracle report   -out DIR                                   re-render DIR/summary.md
//	oracle minimize -out DIR                                   shrink mismatching cases to repro.md
//	oracle selftest                                            check the native harness itself
//	oracle coverage -model M -pkgs bytes.,strings. BIN...     decoder coverage of real Go functions
//	oracle classes -sse                                        the WP-D class regexp (harvest -only)
//	oracle classes -crypto                                     the WP-E class regexp (harvest -only)
package main

import (
	"bufio"
	"debug/elf"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"math/rand/v2"
	"os"
	"regexp"
	"sort"
	"strings"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

func die(f string, a ...any) {
	fmt.Fprintf(os.Stderr, "oracle: "+f+"\n", a...)
	os.Exit(1)
}

func main() {
	if len(os.Args) < 2 {
		die("usage: oracle gen|harvest|run|report|minimize|selftest|coverage [flags]")
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
	case "coverage":
		cmdCoverage(os.Args[2:])
	case "classes":
		// the class regular expression of a mode, for `harvest -only`
		if len(os.Args) > 2 && os.Args[2] == "-sse" {
			fmt.Println(gen.SSERegexp())
		} else if len(os.Args) > 2 && os.Args[2] == "-crypto" {
			fmt.Println(gen.CryptoRegexp())
		} else if len(os.Args) > 2 && os.Args[2] == "-avx" {
			fmt.Println(gen.AVXRegexp())
		} else {
			fmt.Println(gen.V3Regexp())
		}
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
	// flag combinations per word for conditional classes
	condK int
	// MXCSR settings per state for the SSE floating-point classes
	fpK int
}

func newCaseWriter(path string, firstID, condK int) *caseWriter {
	f, err := os.Create(path)
	if err != nil {
		die("%v", err)
	}
	w := bufio.NewWriter(f)
	return &caseWriter{w: w, enc: json.NewEncoder(w), f: f, id: firstID, n: map[string]int{}, condK: condK, fpK: 3}
}

func (cw *caseWriter) emit(class string, b []byte, s gen.State) {
	c := gen.Case(cw.id, class, b, s)
	cw.enc.Encode(&c)
	cw.id++
	cw.n[class]++
}

// add writes k cases of b (conditional classes: condK flag combinations per state).
func (cw *caseWriter) add(r *rand.Rand, class string, b []byte, k int) {
	for j := 0; j < k; j++ {
		s := gen.Setup(r, b)
		if gen.IsX87(b) {
			// a random x87 state and a planted memory operand
			s = gen.SetupX87(r, b)
		}
		if gen.IsFP(gen.Classify(b)) {
			// several MXCSR settings (rounding, FTZ/DAZ, masks, flags) per FP state
			for _, t := range gen.FPVariants(r, s, cw.fpK) {
				cw.emit(class, b, t)
			}
			continue
		}
		if gen.Conditional(gen.Classify(b)) {
			perm := r.Perm(64)
			for f := 0; f < cw.condK; f++ {
				s.RFlags = gen.FlagCombo(perm[f]) | s.RFlags&L.FlagDF
				cw.emit(class, b, s)
			}
			continue
		}
		cw.emit(class, b, s)
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
		fmt.Fprintf(os.Stderr, "  %-32s %7d cases\n", k, cw.n[k])
	}
	fmt.Fprintf(os.Stderr, "  %-32s %7d cases\n", "total", total)
}

func cmdGen(args []string) {
	fs := flag.NewFlagSet("gen", flag.ExitOnError)
	n := fs.Int("n", 600, "encodings per targeted spec (conditional specs: n/4 encodings x -cond flag combinations)")
	ng := fs.Int("group", 40000, "fully random prefix/opcode byte strings")
	condK := fs.Int("cond", 8, "flag combinations per state for conditional classes")
	fpK := fs.Int("fpk", 3, "MXCSR settings per state for the SSE floating-point classes")
	fpOnly := fs.Bool("fp-only", false, "generate only the SSE floating-point specs (gen.FPSpecs, the FP edge families)")
	v3Only := fs.Bool("v3-only", false, "generate only the GOAMD64=v3 extension specs (gen.V3Specs, gen.V3VexSpecs, the FMA edge family)")
	x87Only := fs.Bool("x87-only", false, "generate only the x87 specs and the CET/TLS-call encodings (gen.X87Cases)")
	sseOnly := fs.Bool("sse-only", false, "generate only the SSE packed specs of WP-D (gen.SSESpecs, the SSE edge families)")
	cryptoOnly := fs.Bool("crypto-only", false, "generate only the x86 crypto-extension specs of WP-E (gen.CryptoSpecs, the crypto edge families)")
	avxOnly := fs.Bool("avx-only", false, "generate only the AVX/AVX2/FMA3 specs of WP-F (gen.AVXSpecs, the AVX edge families)")
	avx512Only := fs.Bool("avx512-only", false, "generate only the AVX-512 specs of WP-G (gen.Evex512Specs, the EVEX opcode sweep, -evex-harvest)")
	sweep := fs.Int("sweep", 4, "with -avx512-only: random EVEX encodings per (map, pp, opcode) of the sweep")
	evexHarvest := fs.String("evex-harvest", "", "with -avx512-only: a file of real EVEX/VEX encodings (hex, one per line, optional class after a tab)")
	evexK := fs.Int("evex-k", 24, "with -avx512-only: states per harvested encoding")
	nEdge := fs.Int("edge", 400, "rounds of the hand-targeted edge families (gen.Edges)")
	seed := fs.Uint64("seed", 1, "random seed")
	out := fs.String("o", "gen.jsonl", "output")
	first := fs.Int("first-id", 1_000_000, "first case id")
	fs.Parse(args)
	r := rand.New(rand.NewPCG(*seed, 0x6a616e7573))
	cw := newCaseWriter(*out, *first, *condK)
	cw.fpK = *fpK
	specs, vexSpecs, v3VexSpecs := gen.Specs, gen.VexSpecs, gen.V3VexSpecs
	if *fpOnly {
		specs, vexSpecs, v3VexSpecs = gen.FPSpecs, gen.FPVexSpecs, nil
		*nEdge, *ng = 0, 0
	}
	if *v3Only {
		specs, vexSpecs = gen.V3Specs, nil
		*nEdge, *ng = 0, 0
	}
	if *sseOnly {
		specs, vexSpecs, v3VexSpecs = gen.SSESpecs, nil, nil
		*nEdge, *ng = 0, 0
	}
	if *cryptoOnly {
		specs, vexSpecs, v3VexSpecs = gen.CryptoSpecs, nil, nil
		*nEdge, *ng = 0, 0
	}
	// the WP-F specs: n encodings each in the avx mode, n/4 in the default (full/quick) mode
	avxSpecs, avxN := gen.AVXSpecs, max(*n/4, 1)
	if *avxOnly {
		specs, vexSpecs, v3VexSpecs = nil, nil, nil
		*nEdge, *ng = 0, 0
		avxN = *n
	} else if *fpOnly || *v3Only || *sseOnly || *cryptoOnly || *x87Only {
		avxSpecs = nil
	}
	if *avx512Only {
		specs, vexSpecs, v3VexSpecs, avxSpecs = nil, nil, nil, nil
		*nEdge, *ng = 0, 0
		genAVX512(r, cw, *n, *sweep, *evexHarvest, *evexK)
	}
	if *x87Only {
		specs, vexSpecs, v3VexSpecs = nil, nil, nil
		*nEdge, *ng = 0, 0
	}
	if *x87Only || *nEdge > 0 {
		// the x87 family (every escape-opcode form) and the CET/TLS encodings: n per memory
		// form in x87 mode, a few per form otherwise
		k := max(*nEdge/100, 1)
		if *x87Only {
			k = *n
		}
		for _, e := range gen.X87Cases(r, k) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	for _, sp := range specs {
		nw := *n
		cond := false
		probe := gen.Targeted(r, sp)
		if gen.Conditional(gen.Classify(probe)) {
			nw = (*n + 3) / 4
			cond = true
		}
		_ = cond
		for i := 0; i < nw; i++ {
			b := gen.Targeted(r, sp)
			for !gen.OK(b) {
				b = gen.Targeted(r, sp)
			}
			cw.add(r, "gen/"+gen.Classify(b), b, 1)
		}
	}
	for _, sp := range vexSpecs {
		for i := 0; i < *n; i++ {
			b := gen.VexTargeted(r, sp)
			for !gen.OK(b) {
				b = gen.VexTargeted(r, sp)
			}
			cw.add(r, "gen/"+gen.Classify(b), b, 1)
		}
	}
	for _, sp := range v3VexSpecs {
		for i := 0; i < *n; i++ {
			b := gen.V3Targeted(r, sp)
			for !gen.OK(b) {
				b = gen.V3Targeted(r, sp)
			}
			cw.add(r, "gen/"+gen.Classify(b), b, 1)
		}
	}
	for _, sp := range avxSpecs {
		for i := 0; i < avxN; i++ {
			b := gen.AVXTargeted(r, sp)
			for !gen.OK(b) {
				b = gen.AVXTargeted(r, sp)
			}
			cw.add(r, "gen/"+gen.Classify(b), b, 1)
		}
	}
	if *avxOnly || *nEdge > 0 {
		rounds := max(*nEdge/8, 1)
		if *avxOnly {
			rounds = max(*n/4, 1)
		}
		for _, e := range gen.AVXEdges(r, rounds) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	if *v3Only || *nEdge > 0 {
		rounds := max(*nEdge/8, 1)
		if *v3Only {
			rounds = max(*n/4, 1)
		}
		for _, e := range gen.FMAEdges(r, rounds) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	for _, e := range gen.Edges(r, *nEdge) {
		cw.emit(e.Class, e.Bytes, e.State)
	}
	if *sseOnly || *nEdge > 0 {
		rounds := max(*nEdge/8, 1)
		if *sseOnly {
			rounds = max(*n/4, 1)
		}
		for _, e := range gen.SSEEdges(r, rounds) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	if *cryptoOnly || *nEdge > 0 {
		rounds := max(*nEdge/8, 1)
		if *cryptoOnly {
			rounds = max(*n/2, 1)
		}
		for _, e := range gen.CryptoEdges(r, rounds) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	if *fpOnly || *nEdge > 0 {
		rounds := max(*nEdge/8, 1)
		if *fpOnly {
			rounds = max(*n/2, 1)
		}
		for _, e := range gen.FPEdges(r, rounds) {
			cw.emit(e.Class, e.Bytes, e.State)
		}
	}
	for i := 0; i < *ng; i++ {
		b := gen.GroupRandom(r)
		for !gen.OK(b) {
			b = gen.GroupRandom(r)
		}
		s := gen.Setup(r, b)
		cw.emit("rand/"+gen.Classify(b), b, s)
	}
	cw.close()
}

// funcs returns the [start, end) byte ranges of the functions in .text of an amd64 ELF.
func textInstrs(path string) [][]byte {
	f, err := elf.Open(path)
	if err != nil {
		die("%s: %v", path, err)
	}
	defer f.Close()
	if f.Machine != elf.EM_X86_64 {
		die("%s: not an x86-64 ELF", path)
	}
	text := f.Section(".text")
	if text == nil {
		die("%s: no .text", path)
	}
	data, err := text.Data()
	if err != nil {
		die("%s: %v", path, err)
	}
	syms, err := f.Symbols()
	if err != nil {
		die("%s: no symbol table: %v", path, err)
	}
	type rng struct{ lo, hi uint64 }
	var fns []rng
	for _, s := range syms {
		if elf.ST_TYPE(s.Info) == elf.STT_FUNC && s.Value >= text.Addr && s.Value < text.Addr+text.Size {
			fns = append(fns, rng{s.Value, s.Value + s.Size})
		}
	}
	sort.Slice(fns, func(i, j int) bool { return fns[i].lo < fns[j].lo })
	var out [][]byte
	for i, fn := range fns {
		hi := fn.hi
		if fn.hi == fn.lo {
			hi = text.Addr + text.Size
			if i+1 < len(fns) {
				hi = fns[i+1].lo
			}
		}
		if hi > text.Addr+text.Size {
			hi = text.Addr + text.Size
		}
		b := data[fn.lo-text.Addr : hi-text.Addr]
		for p := 0; p < len(b); {
			if b[p] == 0xCC {
				p++
				continue
			}
			inst, ok := gen.Decode(b[p:min(len(b), p+15)])
			if !ok || inst.Len == 0 {
				p++
				continue
			}
			out = append(out, b[p:p+inst.Len])
			p += inst.Len
		}
	}
	return out
}

func cmdHarvest(args []string) {
	fs := flag.NewFlagSet("harvest", flag.ExitOnError)
	k := fs.Int("k", 3, "random states per harvested instruction")
	condK := fs.Int("cond", 4, "flag combinations per state for conditional classes")
	seed := fs.Uint64("seed", 2, "random seed")
	out := fs.String("o", "harvest.jsonl", "output")
	perClass := fs.Int("per-class", 4000, "keep at most this many distinct instructions per modeled class (0 = all)")
	perOther := fs.Int("per-other", 40, "keep at most this many distinct instructions per unmodeled class (tagged harvest-other/)")
	first := fs.Int("first-id", 1, "first case id")
	fpK := fs.Int("fpk", 2, "MXCSR settings per state for the SSE floating-point classes")
	only := fs.String("only", "", "keep only instructions whose class matches this regular expression (e.g. the vector classes, with a large -k)")
	fsOnly := fs.Bool("fs", false, "keep only FS-prefixed instructions")
	fs.Parse(args)
	var onlyRe *regexp.Regexp
	if *only != "" {
		onlyRe = regexp.MustCompile(*only)
	}
	seen := map[string]bool{}
	var insts [][]byte
	total, forbidden := 0, 0
	for _, p := range fs.Args() {
		for _, b := range textInstrs(p) {
			total++
			key := string(b)
			if seen[key] {
				continue
			}
			seen[key] = true
			if !gen.OK(b) {
				forbidden++
				continue
			}
			if onlyRe != nil && !onlyRe.MatchString(gen.Classify(b)) {
				continue
			}
			if *fsOnly && !hasFSPrefix(b) {
				continue
			}
			insts = append(insts, b)
		}
	}
	fmt.Fprintf(os.Stderr, "harvest: %d instructions, %d distinct, %d forbidden (not run)\n", total, len(seen), forbidden)
	r := rand.New(rand.NewPCG(*seed, 0x6861727665))
	r.Shuffle(len(insts), func(i, j int) { insts[i], insts[j] = insts[j], insts[i] })
	kept, n := insts[:0], map[string]int{}
	for _, b := range insts {
		c := gen.Classify(b)
		limit := *perClass
		if !gen.Modeled[c] {
			limit = *perOther
		}
		if limit == 0 || n[c] < limit {
			n[c]++
			kept = append(kept, b)
		}
	}
	insts = kept
	sort.Slice(insts, func(i, j int) bool { return string(insts[i]) < string(insts[j]) })
	cw := newCaseWriter(*out, *first, *condK)
	cw.fpK = *fpK
	for _, b := range insts {
		c := gen.Classify(b)
		cls := "harvest/" + c
		if !gen.Modeled[c] {
			cls = "harvest-other/" + c
		}
		cw.add(r, cls, b, *k)
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

// hasFSPrefix reports whether b has a 64 (FS) byte among its legacy prefixes.
func hasFSPrefix(b []byte) bool {
	for _, x := range b {
		switch {
		case x == 0x64:
			return true
		case x == 0x66 || x == 0x67 || x == 0xF2 || x == 0xF3 || x == 0xF0 || x == 0x2E || x == 0x3E ||
			x == 0x26 || x == 0x36 || x == 0x65 || x >= 0x40 && x <= 0x4F:
			continue
		}
		return false
	}
	return false
}

// genAVX512 writes the WP-G cases: n encodings of every targeted spec (FP ones under fpK MXCSR
// settings), the opcode sweep, and k states of every harvested encoding.
func genAVX512(r *rand.Rand, cw *caseWriter, n, sweep int, harvest string, k int) {
	for _, sp := range gen.Evex512Specs {
		for i := 0; i < n; i++ {
			b, inf := gen.Evex512Targeted(r, sp)
			if !gen.OK(b) {
				continue
			}
			s := gen.Evex512Setup(r, b, inf, gen.IsEvexFP(sp))
			cw.emit("gen/"+gen.EvexClass(sp, b), b, s)
		}
	}
	for mp := 0; mp < 8; mp++ {
		for pp := 0; pp < 4; pp++ {
			for op := 0; op < 256; op++ {
				for i := 0; i < sweep; i++ {
					b := gen.EvexSweep(r, byte(mp), byte(pp), byte(op))
					s := gen.Evex512Setup(r, b, gen.EvexInfo(b), r.IntN(4) == 0)
					cw.emit(fmt.Sprintf("sweep/evex/%d.%d", mp, pp), b, s)
				}
			}
		}
	}
	if harvest == "" {
		return
	}
	data, err := os.ReadFile(harvest)
	if err != nil {
		die("%v", err)
	}
	for _, line := range strings.Split(string(data), "\n") {
		f := strings.Split(strings.TrimSpace(line), "\t")
		if len(f) == 0 || f[0] == "" {
			continue
		}
		b, err := hex.DecodeString(f[0])
		if err != nil || len(b) == 0 || len(b) > 15 || !gen.OK(b) {
			continue
		}
		cls := "harvest-evex"
		if len(f) > 1 {
			cls += "/" + f[1]
		}
		for j := 0; j < k; j++ {
			cw.emit(cls, b, gen.Evex512Setup(r, b, gen.EvexInfo(b), false))
		}
	}
}
