package main

// oracle coverage: `janus blockers`-style decoder coverage of the Lean x86-64 model over real
// Go amd64 binaries.
//
// Every function symbol of .text is swept linearly with x86asm (INT3 padding skipped), and
// every distinct instruction encoding is run through the Lean model (`janus-oracle-amd64`)
// once. An encoding is accepted iff the model decodes it, with the same length as x86asm
// (any result but `undecodable`). A function is *fully decodable* iff every instruction of its
// sweep is accepted. Functions are split into Go-compiled ones and assembly ones (the
// pclntab file of the entry PC ends in `.s`). The report lists, per binary, the function
// counts, the instruction-occurrence coverage and the most frequent rejected encodings.

import (
	"debug/elf"
	"debug/gosym"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

type covFunc struct {
	name  string
	asm   bool
	insts [][]byte
}

func binFuncs(path string) []covFunc {
	f, err := elf.Open(path)
	if err != nil {
		die("%s: %v", path, err)
	}
	defer f.Close()
	text := f.Section(".text")
	data, err := text.Data()
	if err != nil {
		die("%s: %v", path, err)
	}
	var tab *gosym.Table
	if pcln := f.Section(".gopclntab"); pcln != nil {
		pd, _ := pcln.Data()
		lt := gosym.NewLineTable(pd, text.Addr)
		tab, _ = gosym.NewTable(nil, lt)
	}
	syms, err := f.Symbols()
	if err != nil {
		die("%s: %v", path, err)
	}
	type rng struct {
		name   string
		lo, hi uint64
	}
	var fns []rng
	for _, s := range syms {
		if elf.ST_TYPE(s.Info) == elf.STT_FUNC && s.Value >= text.Addr && s.Value < text.Addr+text.Size {
			fns = append(fns, rng{s.Name, s.Value, s.Value + s.Size})
		}
	}
	sort.Slice(fns, func(i, j int) bool { return fns[i].lo < fns[j].lo })
	var out []covFunc
	for i, fn := range fns {
		hi := fn.hi
		if hi == fn.lo {
			hi = text.Addr + text.Size
			if i+1 < len(fns) {
				hi = fns[i+1].lo
			}
		}
		hi = min(hi, text.Addr+text.Size)
		cf := covFunc{name: fn.name}
		if tab != nil {
			if file, _, _ := tab.PCToLine(fn.lo); strings.HasSuffix(file, ".s") {
				cf.asm = true
			}
		}
		b := data[fn.lo-text.Addr : hi-text.Addr]
		for p := 0; p < len(b); {
			if b[p] == 0xCC {
				p++
				continue
			}
			inst, ok := gen.Decode(b[p:min(len(b), p+15)])
			if !ok || inst.Len == 0 {
				cf.insts = append(cf.insts, b[p:p+1])
				p++
				continue
			}
			cf.insts = append(cf.insts, b[p:p+inst.Len])
			p += inst.Len
		}
		out = append(out, cf)
	}
	return out
}

type covStats struct {
	funcs, full int
}

func cmdCoverage(args []string) {
	fs := flag.NewFlagSet("coverage", flag.ExitOnError)
	model := fs.String("model", ".lake/build/bin/janus-oracle-amd64", "the Lean model executable")
	prefixes := fs.String("pkgs", "", "comma-separated symbol prefixes to report separately (e.g. sync/atomic.,bytes.)")
	top := fs.Int("top", 15, "rejected encodings to list per binary")
	jsonOut := fs.String("json", "", "also write the per-binary numbers as JSON here")
	jobs := fs.Int("j", 16, "model processes")
	showEnc := fs.Bool("show-enc", false, "with -show: also list the distinct rejected encodings")
	show := fs.String("show", "", "comma-separated symbol prefixes: list the rejected classes of each matching function")
	fs.Parse(args)
	type binRes struct {
		Binary                   string
		Go, GoFull, Asm, AsmFull int
		Occ, OccOK               int
		Distinct, DistinctOK     int
		Pkg                      map[string][2]int
		Blockers                 []string
		// SoleBlockers: per instruction class (mnemonic, `fs:` marked), the number of
		// functions in which it is the only rejected class (accepting it would make them
		// fully decodable), and its rejected occurrences.
		SoleBlockers []string
	}
	var results []binRes
	for _, path := range fs.Args() {
		fns := binFuncs(path)
		distinct := map[string]bool{}
		var keys []string
		for _, f := range fns {
			for _, b := range f.insts {
				k := string(b)
				if !distinct[k] {
					distinct[k] = true
					keys = append(keys, k)
				}
			}
		}
		cases := make([]L.Case, 0, len(keys))
		for i, k := range keys {
			var s gen.State
			s.Regs[4] = L.DataBase + 2048
			cases = append(cases, gen.Case(i, "cov", []byte(k), s))
		}
		ms := make([]L.Model, len(cases))
		var wg sync.WaitGroup
		chunk := (len(cases) + *jobs - 1) / *jobs
		for lo := 0; lo < len(cases); lo += chunk {
			hi := min(lo+chunk, len(cases))
			wg.Add(1)
			go func(lo, hi int) {
				defer wg.Done()
				out, stderr, err := pipeThrough[L.Model]([]string{*model}, nil, cases[lo:hi])
				if err != nil || len(out) != hi-lo {
					die("model: %v (%d/%d results): %s", err, len(out), hi-lo, stderr)
				}
				copy(ms[lo:hi], out)
			}(lo, hi)
		}
		wg.Wait()
		ok := map[string]bool{}
		for i, m := range ms {
			k := keys[i]
			ok[k] = m.Fault != "undecodable" && m.Len == len(k)
		}
		r := binRes{Binary: filepath.Base(path), Distinct: len(keys), Pkg: map[string][2]int{}}
		for _, k := range keys {
			if ok[k] {
				r.DistinctOK++
			}
		}
		rej := map[string]int{}
		rejFn := map[string]int{}
		sole := map[string]int{}
		clsOcc := map[string]int{}
		for _, f := range fns {
			full := true
			for _, b := range f.insts {
				r.Occ++
				if ok[string(b)] {
					r.OccOK++
				} else {
					full = false
					rej[string(b)]++
				}
			}
			if !full {
				cls := map[string]bool{}
				for _, b := range f.insts {
					if !ok[string(b)] {
						rejFn[string(b)]++
						c := blockClass(b)
						cls[c] = true
						clsOcc[c]++
					}
				}
				if len(cls) == 1 {
					for c := range cls {
						sole[c]++
					}
				}
				for _, p := range strings.Split(*show, ",") {
					if p != "" && strings.HasPrefix(f.name, p) {
						var cs []string
						for c := range cls {
							cs = append(cs, c)
						}
						sort.Strings(cs)
						fmt.Printf("  blocked %-50s %s\n", f.name, strings.Join(cs, " "))
						if *showEnc {
							seenE := map[string]bool{}
							for _, b := range f.insts {
								if !ok[string(b)] && !seenE[string(b)] {
									seenE[string(b)] = true
									fmt.Printf("      %-24s %s\n", hex.EncodeToString(b), gen.Asm(b))
								}
							}
						}
						break
					}
				}
			}
			if f.asm {
				r.Asm++
				if full {
					r.AsmFull++
				}
			} else {
				r.Go++
				if full {
					r.GoFull++
				}
			}
			for _, p := range strings.Split(*prefixes, ",") {
				if p != "" && strings.HasPrefix(f.name, p) {
					v := r.Pkg[p]
					v[0]++
					if full {
						v[1]++
					}
					r.Pkg[p] = v
				}
			}
		}
		var rk []string
		for k := range rej {
			rk = append(rk, k)
		}
		sort.Slice(rk, func(i, j int) bool {
			if rej[rk[i]] != rej[rk[j]] {
				return rej[rk[i]] > rej[rk[j]]
			}
			return rk[i] < rk[j]
		})
		for i, k := range rk {
			if i >= *top {
				break
			}
			r.Blockers = append(r.Blockers, fmt.Sprintf("%6d  %-24s %s", rej[k], hex.EncodeToString([]byte(k)), gen.Asm([]byte(k))))
		}
		var ck []string
		for k := range clsOcc {
			ck = append(ck, k)
		}
		sort.Slice(ck, func(i, j int) bool {
			if sole[ck[i]] != sole[ck[j]] {
				return sole[ck[i]] > sole[ck[j]]
			}
			if clsOcc[ck[i]] != clsOcc[ck[j]] {
				return clsOcc[ck[i]] > clsOcc[ck[j]]
			}
			return ck[i] < ck[j]
		})
		for i, k := range ck {
			if i >= *top {
				break
			}
			r.SoleBlockers = append(r.SoleBlockers, fmt.Sprintf("%5d sole  %6d occ  %s", sole[k], clsOcc[k], k))
		}
		results = append(results, r)
		fmt.Printf("== %s\n", r.Binary)
		fmt.Printf("functions: Go-compiled %d, fully decodable %d (%.1f%%); assembly %d, fully decodable %d (%.1f%%)\n",
			r.Go, r.GoFull, pct(r.GoFull, r.Go), r.Asm, r.AsmFull, pct(r.AsmFull, r.Asm))
		fmt.Printf("instructions: %d occurrences, %.2f%% accepted; %d distinct, %.2f%% accepted\n",
			r.Occ, pct(r.OccOK, r.Occ), r.Distinct, pct(r.DistinctOK, r.Distinct))
		var ps []string
		for p := range r.Pkg {
			ps = append(ps, p)
		}
		sort.Strings(ps)
		for _, p := range ps {
			fmt.Printf("  %-16s %5d functions, %5d fully decodable\n", p, r.Pkg[p][0], r.Pkg[p][1])
		}
		fmt.Printf("rejected classes (functions where it is the only blocker, occurrences):\n")
		for _, l := range r.SoleBlockers {
			fmt.Println("  " + l)
		}
		fmt.Printf("top rejected encodings (occurrences):\n")
		for _, l := range r.Blockers {
			fmt.Println("  " + l)
		}
	}
	if *jsonOut != "" {
		b, _ := json.MarshalIndent(results, "", "  ")
		os.WriteFile(*jsonOut, b, 0o644)
	}
}

// blockClass names the instruction class of a rejected encoding: the x86asm mnemonic, with
// `fs:`/`gs:` for segment-relative accesses, `/vex` and `/evex` for those encodings and the
// vector length; `(bad)` if x86asm cannot decode it either.
func blockClass(b []byte) string {
	inst, ok := gen.Decode(b)
	if !ok {
		return "(bad)"
	}
	c := strings.ToLower(inst.Op.String())
	for _, p := range inst.Prefix {
		switch p &^ 0xF000 {
		case 0x64:
			c = "fs:" + c
		case 0x65:
			c = "gs:" + c
		}
	}
	i := 0
	for i < len(b) && (b[i] == 0x66 || b[i] == 0xF2 || b[i] == 0xF3 || b[i] == 0x64 || b[i] == 0x65 || b[i] == 0x67 || (b[i] >= 0x40 && b[i] <= 0x4F)) {
		i++
	}
	if i < len(b) {
		switch {
		case b[i] == 0x62:
			c += "/evex"
		case b[i] == 0xC5 && i+1 < len(b):
			c += map[bool]string{true: "/vex256", false: "/vex128"}[b[i+1]&4 != 0]
		case b[i] == 0xC4 && i+2 < len(b):
			c += map[bool]string{true: "/vex256", false: "/vex128"}[b[i+2]&4 != 0]
		}
	}
	return c
}

func pct(a, b int) float64 {
	if b == 0 {
		return 0
	}
	return 100 * float64(a) / float64(b)
}
