package main

import (
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// cmdMinimize shrinks one mismatching case per distinct encoding: it repeatedly tries to
// set each input (registers, XMM registers, flags, seed, init bytes) to a default value and
// keeps the change while the case still mismatches.
func cmdMinimize(args []string) {
	fs := flag.NewFlagSet("minimize", flag.ExitOnError)
	outDir := fs.String("out", "oracle-out", "output directory of a previous run")
	maxN := fs.Int("max", 100, "distinct mismatching encodings to minimize")
	var o runOpts
	fs.StringVar(&o.runner, "runner", "oracle-amd64/bin/runner", "native runner")
	fs.StringVar(&o.model, "model", ".lake/build/bin/janus-oracle-amd64", "janus-oracle-amd64 executable")
	fs.Parse(args)
	cases := readJSONL[L.Case](filepath.Join(*outDir, "cases.jsonl"))
	byID := map[int]L.Case{}
	for _, c := range cases {
		byID[c.ID] = c
	}
	var picked []L.Case
	seen := map[string]bool{}
	for _, v := range readJSONL[Verdict](filepath.Join(*outDir, "verdicts.jsonl")) {
		if v.Verdict == Mismatch && !seen[v.Bytes] && len(picked) < *maxN {
			seen[v.Bytes] = true
			picked = append(picked, byID[v.ID])
		}
	}
	defSP := fmt.Sprintf("%#x", L.DataBase+2048)
	cur := picked
	for round := 0; round < 60; round++ {
		var cands []L.Case
		owner := map[int]int{}
		id := 1
		for i, c := range cur {
			for f := 0; f < 36; f++ {
				n := c
				n.Regs = c.Regs
				n.XMM = c.XMM
				changed := false
				switch {
				case f < 16:
					want := "0x0"
					if f == 4 {
						want = defSP
					}
					if n.Regs[f] != want {
						n.Regs[f], changed = want, true
					}
				case f < 32:
					if n.XMM[f-16] != "0x0" {
						n.XMM[f-16], changed = "0x0", true
					}
				case f == 32:
					if n.RFlags != 0 {
						n.RFlags, changed = 0, true
					}
				case f == 33:
					if n.Seed != 0 {
						n.Seed, changed = 0, true
					}
				case f == 34:
					if len(n.Init) > 0 {
						n.Init, changed = nil, true
					}
				}
				if changed {
					n.ID = id
					owner[id] = i
					id++
					cands = append(cands, n)
				}
			}
		}
		if len(cands) == 0 {
			break
		}
		hw := runNative(o, cands)
		md := runModel(o, cands)
		hb, mb := index(hw, md)
		progress := false
		took := map[int]bool{}
		for _, c := range cands {
			i := owner[c.ID]
			if took[i] {
				continue
			}
			if compareCase(&c, hb[c.ID], mb[c.ID]).Verdict == Mismatch {
				keep := c
				keep.ID = cur[i].ID
				cur[i] = keep
				took[i] = true
				progress = true
			}
		}
		if !progress {
			break
		}
	}
	hw := runNative(o, cur)
	md := runModel(o, cur)
	hb, mb := index(hw, md)
	var b strings.Builder
	fmt.Fprintf(&b, "# Minimal reproductions (amd64)\n\nEach case: one instruction at pc %#x, data buffer [%#x, %#x) filled with layout.Pattern(seed, i), then init overrides.\nOnly non-default inputs are listed; every other register is 0, RSP = %s, XMM = 0 unless listed.\n\n", L.TestPC, L.DataBase, L.DataBase+L.DataSize, defSP)
	sort.Slice(cur, func(i, j int) bool { return cur[i].Bytes < cur[j].Bytes })
	for i := range cur {
		c := cur[i]
		v := compareCase(&c, hb[c.ID], mb[c.ID])
		fmt.Fprintf(&b, "## `%s` `%s` (%s, %s)\n\n", c.Bytes, disasm(c.Bytes), c.Class, v.Verdict)
		var in []string
		for r, x := range c.Regs {
			if (r == 4 && x != defSP) || (r != 4 && x != "0x0") {
				in = append(in, regNames[r]+"="+x)
			}
		}
		for r, x := range c.XMM {
			if x != "0x0" {
				in = append(in, fmt.Sprintf("xmm%d=%s", r, x))
			}
		}
		in = append(in, "rflags="+flagString(c.RFlags), fmt.Sprintf("seed=%d", c.Seed))
		if len(c.Init) > 0 {
			in = append(in, fmt.Sprintf("init=%v", c.Init))
		}
		fmt.Fprintf(&b, "* input: %s\n", strings.Join(in, " "))
		for _, d := range v.Diffs {
			fmt.Fprintf(&b, "* %s\n", d)
		}
		fmt.Fprintf(&b, "\n")
	}
	writeJSONL(filepath.Join(*outDir, "repro.jsonl"), cur)
	os.WriteFile(filepath.Join(*outDir, "repro.md"), []byte(b.String()), 0o644)
	fmt.Print(b.String())
}

func index(hw []L.HW, md []L.Model) (map[int]*L.HW, map[int]*L.Model) {
	hb := map[int]*L.HW{}
	for i := range hw {
		hb[hw[i].ID] = &hw[i]
	}
	mb := map[int]*L.Model{}
	for i := range md {
		mb[md[i].ID] = &md[i]
	}
	return hb, mb
}
