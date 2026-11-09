package main

import (
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

// cmdMinimize shrinks one mismatching case per distinct word: it repeatedly tries to set
// each input register (and NZCV, seed) to 0 and keeps the change when the case still
// mismatches. The result is a reproduction whose nonzero inputs are the ones that matter.
func cmdMinimize(args []string) {
	fs := flag.NewFlagSet("minimize", flag.ExitOnError)
	outDir := fs.String("out", "oracle-out", "output directory of a previous run")
	maxWords := fs.Int("max", 100, "distinct mismatching words to minimize")
	var o runOpts
	fs.StringVar(&o.qemu, "qemu", "/usr/bin/qemu-aarch64", "qemu-aarch64")
	fs.StringVar(&o.runner, "runner", "oracle/bin/runner", "native runner")
	fs.StringVar(&o.model, "model", ".lake/build/bin/janus-oracle", "janus-oracle executable")
	fs.Parse(args)
	cases := readJSONL[L.Case](filepath.Join(*outDir, "cases.jsonl"))
	byID := map[int]L.Case{}
	for _, c := range cases {
		byID[c.ID] = c
	}
	var picked []L.Case
	seen := map[string]bool{}
	for _, v := range readJSONL[Verdict](filepath.Join(*outDir, "verdicts.jsonl")) {
		if v.Verdict == Mismatch && !seen[v.Word] && len(picked) < *maxWords {
			seen[v.Word] = true
			picked = append(picked, byID[v.ID])
		}
	}
	// Each round: for every current case, candidates zeroing one more input; evaluate all in
	// one batch; keep, per case, the first candidate that still mismatches.
	cur := picked
	for round := 0; round < 40; round++ {
		var cands []L.Case
		owner := map[int]int{}
		id := 1
		for i, c := range cur {
			for f := 0; f < 34; f++ {
				n := c
				changed := false
				switch {
				case f < 31:
					if n.X[f] != "0x0" {
						n.X[f], changed = "0x0", true
					}
				case f == 31:
					if n.NZCV != 0 {
						n.NZCV, changed = 0, true
					}
				case f == 32:
					if n.Seed != 0 {
						n.Seed, changed = 0, true
					}
				case f == 33:
					if n.SP != fmt.Sprintf("%#x", L.DataBase+2048) {
						n.SP, changed = fmt.Sprintf("%#x", L.DataBase+2048), true
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
		hb := map[int]*L.HW{}
		for i := range hw {
			hb[hw[i].ID] = &hw[i]
		}
		mb := map[int]*L.Model{}
		for i := range md {
			mb[md[i].ID] = &md[i]
		}
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
	// Final evaluation for the report.
	hw := runNative(o, cur)
	md := runModel(o, cur)
	asm := disasm(cur)
	var b strings.Builder
	fmt.Fprintf(&b, "# Minimal reproductions\n\nEach case: one instruction at pc %#x, data buffer [%#x, %#x) filled with layout.Pattern(seed, i).\nOnly nonzero inputs are listed; every other X register is 0, SP = %#x unless listed.\n\n", L.TestPC, L.DataBase, L.DataBase+L.DataSize, L.DataBase+2048)
	sort.Slice(cur, func(i, j int) bool { return cur[i].Word < cur[j].Word })
	hb := map[int]*L.HW{}
	for i := range hw {
		hb[hw[i].ID] = &hw[i]
	}
	mb := map[int]*L.Model{}
	for i := range md {
		mb[md[i].ID] = &md[i]
	}
	for i := range cur {
		c := cur[i]
		v := compareCase(&c, hb[c.ID], mb[c.ID])
		fmt.Fprintf(&b, "## `%s` `%s` (%s, %s)\n\n", c.Word, asm[c.Word], c.Class, v.Verdict)
		var in []string
		for r, x := range c.X {
			if x != "0x0" {
				in = append(in, fmt.Sprintf("x%d=%s", r, x))
			}
		}
		in = append(in, "sp="+c.SP, fmt.Sprintf("nzcv=%04b", c.NZCV), fmt.Sprintf("seed=%d", c.Seed))
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
