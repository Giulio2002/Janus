// Command janus-coverage measures how much of Go (and cgo's C) the Janus decoders accept, and
// which runtime entry points have contracts. Driven by scripts/coverage.sh; see docs/COVERAGE.md.
//
//	janus-coverage insn -arch A -decode D -model M [-json F] [-calls F] [-c] BINARY_OR_OBJECT...
//	janus-coverage runtime -goroot G -repo R -branches "main agent/x" [-o F]
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"sort"
	"strings"
)

func main() {
	if len(os.Args) < 2 {
		die("usage: janus-coverage insn|runtime ...")
	}
	switch os.Args[1] {
	case "insn":
		cmdInsn(os.Args[2:])
	case "runtime":
		cmdRuntime(os.Args[2:])
	default:
		die("unknown command %s", os.Args[1])
	}
}

// agg is one function name, aggregated over every binary containing it.
type agg struct {
	Name, Pkg, Kind string
	Instances       int
	Occ, OccOK      int             // from the first instance
	Rejected        map[string]bool // union over instances
}

type row struct {
	Key      string
	Funcs    int // functions it blocks (any)
	Sole     int // functions in which it is the only rejected class
	Occ      int
	Family   string
	Example  string
	ExampleF string
}

func cmdInsn(args []string) {
	fs := flag.NewFlagSet("insn", flag.ExitOnError)
	arch := fs.String("arch", "arm64", "arm64 | amd64")
	dec := fs.String("decode", ".lake/build/bin/janus-decode", "janus-decode")
	model := fs.String("model", ".lake/build/bin/janus-oracle-amd64", "janus-oracle-amd64")
	jobs := fs.Int("j", 8, "decoder processes")
	jsonOut := fs.String("json", "", "write the aggregate as JSON")
	callsOut := fs.String("calls", "", "write the assembly-callee table here (Go binaries)")
	cMode := fs.Bool("c", false, "inputs are C objects: key functions by object/function, not by name")
	top := fs.Int("top", 40, "rows per ranking")
	cache := fs.String("cache", "", "verdict cache file (valid for one decoder executable)")
	fs.Parse(args)
	d := &Decoder{Arch: *arch, Decode: *dec, Model: *model, Jobs: *jobs}
	if *cache != "" {
		d.LoadCache(*cache)
		defer d.SaveCache(*cache)
	}

	funcs := map[string]*agg{}
	var order []string
	// assembly callees: asm name -> set of Go-compiled caller names (direct, or through an ABI wrapper)
	asmCallers := map[string]map[string]bool{}
	wrapperOf := map[string]bool{}
	for _, p := range fs.Args() {
		img, err := loadImage(p)
		if err != nil {
			die("%v", err)
		}
		if img.Arch != *arch {
			die("%s is %s, not %s", p, img.Arch, *arch)
		}
		keys := map[string]struct{}{}
		for _, f := range img.Funcs {
			for _, b := range f.Insts {
				keys[string(b)] = struct{}{}
			}
		}
		d.Resolve(keys)
		for _, f := range img.Funcs {
			name := f.Name
			if *cMode {
				name = f.Pkg + ":" + f.Name
			}
			a := funcs[name]
			if a == nil {
				a = &agg{Name: name, Pkg: f.Pkg, Kind: f.Kind, Rejected: map[string]bool{}}
				funcs[name] = a
				order = append(order, name)
				for _, b := range f.Insts {
					a.Occ++
					if d.Accepted(string(b)) {
						a.OccOK++
					}
				}
			}
			a.Instances++
			for _, b := range f.Insts {
				if !d.Accepted(string(b)) {
					a.Rejected[string(b)] = true
				}
			}
		}
		// direct calls from Go-compiled code into assembly
		for _, f := range img.Funcs {
			if f.Kind != KindGo {
				continue
			}
			for _, t := range f.Calls {
				g := img.byAdr[t]
				if g == nil {
					continue
				}
				target := ""
				switch g.Kind {
				case KindAsm:
					target = g.Name
				case KindWrapper:
					// an ABI wrapper `F` of assembly `F.abi0`
					for _, t2 := range g.Calls {
						if h := img.byAdr[t2]; h != nil && h.Kind == KindAsm && strings.TrimSuffix(h.Name, ".abi0") == g.Name {
							target = h.Name
							wrapperOf[h.Name] = true
						}
					}
				}
				if target == "" {
					continue
				}
				if asmCallers[target] == nil {
					asmCallers[target] = map[string]bool{}
				}
				asmCallers[target][f.Name] = true
			}
		}
	}

	cls := func(k string) (string, string) {
		if *arch == "arm64" {
			return classArm64(k)
		}
		return classAmd64(k)
	}
	classCache := map[string][2]string{}
	classOf := func(k string) (string, string) {
		if c, ok := classCache[k]; ok {
			return c[0], c[1]
		}
		c, f := cls(k)
		classCache[k] = [2]string{c, f}
		return c, f
	}

	kinds := []string{KindGo, KindAsm, KindWrapper, KindTest, KindC}
	type sum struct{ N, Full, Occ, OccOK int }
	sums := map[string]*sum{}
	pkgs := map[string]map[string]*sum{} // kind -> pkg -> sum
	rank := map[string]map[string]*row{} // kind -> class -> row
	famRank := map[string]map[string]*row{}
	encRank := map[string]map[string]*row{}
	for _, k := range kinds {
		sums[k] = &sum{}
		pkgs[k] = map[string]*sum{}
		rank[k], famRank[k], encRank[k] = map[string]*row{}, map[string]*row{}, map[string]*row{}
	}
	bump := func(m map[string]*row, key, fam, ex, exf string, sole bool) {
		r := m[key]
		if r == nil {
			r = &row{Key: key, Family: fam, Example: ex, ExampleF: exf}
			m[key] = r
		}
		r.Funcs++
		if sole {
			r.Sole++
		}
	}
	for _, n := range order {
		a := funcs[n]
		s := sums[a.Kind]
		s.N++
		s.Occ += a.Occ
		s.OccOK += a.OccOK
		ps := pkgs[a.Kind][a.Pkg]
		if ps == nil {
			ps = &sum{}
			pkgs[a.Kind][a.Pkg] = ps
		}
		ps.N++
		if len(a.Rejected) == 0 {
			s.Full++
			ps.Full++
			continue
		}
		classes := map[string]string{}
		fams := map[string]bool{}
		for k := range a.Rejected {
			c, f := classOf(k)
			if _, seen := classes[c]; !seen || k < classes[c] {
				classes[c] = k
			}
			fams[f] = true
		}
		for c, k := range classes {
			_, f := classOf(k)
			bump(rank[a.Kind], c, f, k, a.Name, len(classes) == 1)
		}
		for f := range fams {
			bump(famRank[a.Kind], f, f, "", a.Name, len(fams) == 1)
		}
		for k := range a.Rejected {
			c, f := classOf(k)
			bump(encRank[a.Kind], k, f+" | "+c, k, a.Name, len(a.Rejected) == 1)
		}
	}

	out := os.Stdout
	fmt.Fprintf(out, "## %s: %d inputs, %d distinct functions, %d distinct encodings decoded\n\n", *arch, len(fs.Args()), len(order), len(d.ok))
	fmt.Fprintf(out, "| kind | functions | fully decodable | %% | instructions accepted |\n|---|---:|---:|---:|---:|\n")
	for _, k := range kinds {
		s := sums[k]
		if s.N == 0 {
			continue
		}
		fmt.Fprintf(out, "| %s | %d | %d | %.2f%% | %.3f%% |\n", k, s.N, s.Full, pct(s.Full, s.N), pct(s.OccOK, s.Occ))
	}
	fmt.Fprintln(out)
	for _, k := range kinds {
		if sums[k].N == 0 || sums[k].N == sums[k].Full {
			continue
		}
		fmt.Fprintf(out, "### %s: ISA families, by functions blocked\n\n| family | functions blocked | sole blocker |\n|---|---:|---:|\n", k)
		for _, r := range sortRows(famRank[k], 100) {
			fmt.Fprintf(out, "| %s | %d | %d |\n", r.Key, r.Funcs, r.Sole)
		}
		fmt.Fprintf(out, "\n### %s: rejected classes (mnemonic), by functions blocked\n\n| class | family | functions blocked | sole blocker | example encoding | example function |\n|---|---|---:|---:|---|---|\n", k)
		for _, r := range sortRows(rank[k], *top) {
			fmt.Fprintf(out, "| `%s` | %s | %d | %d | `%s` `%s` | `%s` |\n", r.Key, r.Family, r.Funcs, r.Sole, hexKey(*arch, r.Example), asmText(*arch, r.Example), r.ExampleF)
		}
		fmt.Fprintf(out, "\n### %s: rejected encodings, by functions blocked\n\n| encoding | disassembly | family / class | functions blocked | sole |\n|---|---|---|---:|---:|\n", k)
		for _, r := range sortRows(encRank[k], *top) {
			fmt.Fprintf(out, "| `%s` | `%s` | %s | %d | %d |\n", hexKey(*arch, r.Key), asmText(*arch, r.Key), r.Family, r.Funcs, r.Sole)
		}
		fmt.Fprintln(out)
	}
	for _, k := range []string{KindGo, KindAsm, KindC} {
		if len(pkgs[k]) == 0 {
			continue
		}
		fmt.Fprintf(out, "### %s: per package (ascending %%)\n\n| package | functions | fully decodable | %% |\n|---|---:|---:|---:|\n", k)
		var ps []string
		for p := range pkgs[k] {
			ps = append(ps, p)
		}
		sort.Slice(ps, func(i, j int) bool {
			a, b := pkgs[k][ps[i]], pkgs[k][ps[j]]
			pa, pb := pct(a.Full, a.N), pct(b.Full, b.N)
			if pa != pb {
				return pa < pb
			}
			return ps[i] < ps[j]
		})
		for _, p := range ps {
			s := pkgs[k][p]
			fmt.Fprintf(out, "| %s | %d | %d | %.1f%% |\n", p, s.N, s.Full, pct(s.Full, s.N))
		}
		fmt.Fprintln(out)
	}

	if *callsOut != "" && len(asmCallers) > 0 {
		var names []string
		for n := range asmCallers {
			names = append(names, n)
		}
		sort.Slice(names, func(i, j int) bool {
			if len(asmCallers[names[i]]) != len(asmCallers[names[j]]) {
				return len(asmCallers[names[i]]) > len(asmCallers[names[j]])
			}
			return names[i] < names[j]
		})
		var sb strings.Builder
		fmt.Fprintf(&sb, "## %s: assembly functions called directly by Go-compiled std code\n\n", *arch)
		fmt.Fprintf(&sb, "| assembly function | package | Go callers | via ABI0 wrapper | fully decodes | blocking families (classes) |\n|---|---|---:|---|---|---|\n")
		for _, n := range names {
			a := funcs[n]
			full := "yes"
			blk := ""
			if a != nil && len(a.Rejected) > 0 {
				full = "no"
				fams := map[string]map[string]bool{}
				for k := range a.Rejected {
					c, f := classOf(k)
					if fams[f] == nil {
						fams[f] = map[string]bool{}
					}
					fams[f][c] = true
				}
				var parts []string
				for f, cs := range fams {
					var cl []string
					for c := range cs {
						cl = append(cl, c)
					}
					sort.Strings(cl)
					if len(cl) > 6 {
						cl = append(cl[:6], fmt.Sprintf("+%d", len(cl)-6))
					}
					parts = append(parts, fmt.Sprintf("%s (%s)", f, strings.Join(cl, ", ")))
				}
				sort.Strings(parts)
				blk = strings.Join(parts, "; ")
			}
			pkg := ""
			if a != nil {
				pkg = a.Pkg
			}
			w := ""
			if wrapperOf[n] {
				w = "yes"
			}
			fmt.Fprintf(&sb, "| `%s` | %s | %d | %s | %s | %s |\n", n, pkg, len(asmCallers[n]), w, full, blk)
		}
		os.WriteFile(*callsOut, []byte(sb.String()), 0o644)
	}

	if *jsonOut != "" {
		type jf struct {
			Name, Pkg, Kind string
			Full            bool
			Classes         []string
			Families        []string
		}
		var all []jf
		for _, n := range order {
			a := funcs[n]
			cs, fs := map[string]bool{}, map[string]bool{}
			for k := range a.Rejected {
				c, f := classOf(k)
				cs[c] = true
				fs[f] = true
			}
			var cl, fl []string
			for c := range cs {
				cl = append(cl, c)
			}
			for f := range fs {
				fl = append(fl, f)
			}
			sort.Strings(cl)
			sort.Strings(fl)
			all = append(all, jf{a.Name, a.Pkg, a.Kind, len(a.Rejected) == 0, cl, fl})
		}
		b, _ := json.Marshal(map[string]any{"arch": *arch, "summary": sums, "functions": all})
		os.WriteFile(*jsonOut, b, 0o644)
	}
}

func sortRows(m map[string]*row, n int) []*row {
	var rs []*row
	for _, r := range m {
		rs = append(rs, r)
	}
	sort.Slice(rs, func(i, j int) bool {
		if rs[i].Funcs != rs[j].Funcs {
			return rs[i].Funcs > rs[j].Funcs
		}
		if rs[i].Sole != rs[j].Sole {
			return rs[i].Sole > rs[j].Sole
		}
		return rs[i].Key < rs[j].Key
	})
	if len(rs) > n {
		rs = rs[:n]
	}
	return rs
}

func pct(a, b int) float64 {
	if b == 0 {
		return 0
	}
	return 100 * float64(a) / float64(b)
}
