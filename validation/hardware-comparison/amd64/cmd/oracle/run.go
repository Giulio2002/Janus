package main

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

type runOpts struct {
	runner, model string
	jobs, shard   int
}

// pipeThrough runs argv with the cases on stdin and decodes one T per output line.
func pipeThrough[T any](argv []string, env []string, cases []L.Case) ([]T, string, error) {
	cmd := exec.Command(argv[0], argv[1:]...)
	cmd.Env = append(os.Environ(), env...)
	stdin, _ := cmd.StdinPipe()
	stdout, _ := cmd.StdoutPipe()
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Start(); err != nil {
		return nil, "", err
	}
	go func() {
		w := bufio.NewWriter(stdin)
		enc := json.NewEncoder(w)
		for i := range cases {
			enc.Encode(&cases[i])
		}
		w.Flush()
		stdin.Close()
	}()
	var out []T
	sc := bufio.NewScanner(stdout)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		var v T
		if err := json.Unmarshal(sc.Bytes(), &v); err != nil {
			break
		}
		out = append(out, v)
	}
	io.Copy(io.Discard, stdout)
	err := cmd.Wait()
	return out, stderr.String(), err
}

// runNative runs cases through the native runner, restarting it after a case it died on.
func runNative(o runOpts, cases []L.Case) []L.HW {
	var res []L.HW
	for len(cases) > 0 {
		out, stderr, err := pipeThrough[L.HW]([]string{o.runner}, []string{"GODEBUG=asyncpreemptoff=1"}, cases)
		res = append(res, out...)
		if len(out) >= len(cases) {
			break
		}
		bad := cases[len(out)]
		note := fmt.Sprintf("runner died: %v: %s", err, strings.TrimSpace(stderr))
		if len(note) > 300 {
			note = note[:300]
		}
		res = append(res, L.HW{ID: bad.ID, Status: "error", Note: note})
		cases = cases[len(out)+1:]
	}
	return res
}

// runModel runs the Lean model; if it dies mid-shard the rest of the shard is retried
// after the case it died on.
func runModel(o runOpts, cases []L.Case) []L.Model {
	var res []L.Model
	for len(cases) > 0 {
		out, stderr, err := pipeThrough[L.Model]([]string{o.model}, nil, cases)
		res = append(res, out...)
		if len(out) >= len(cases) {
			break
		}
		fmt.Fprintf(os.Stderr, "oracle: model produced %d/%d results (%v): %s\n", len(out), len(cases), err, strings.TrimSpace(stderr))
		cases = cases[len(out)+1:]
	}
	return res
}

func cmdRun(args []string) {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	casesF := fs.String("cases", "", "comma-separated case files")
	outDir := fs.String("out", "oracle-out", "output directory")
	var o runOpts
	fs.StringVar(&o.runner, "runner", "oracle-amd64/bin/runner", "native runner")
	fs.StringVar(&o.model, "model", ".lake/build/bin/janus-oracle-amd64", "janus-oracle-amd64 executable")
	fs.IntVar(&o.jobs, "j", 16, "parallel shards")
	fs.IntVar(&o.shard, "shard", 4000, "cases per shard")
	skipNative := fs.Bool("reuse-native", false, "reuse DIR/hw.jsonl from a previous run (the model changed, hardware did not)")
	fs.Parse(args)
	var cases []L.Case
	for _, p := range strings.Split(*casesF, ",") {
		if p != "" {
			cases = append(cases, readJSONL[L.Case](p)...)
		}
	}
	if len(cases) == 0 {
		die("no cases")
	}
	os.MkdirAll(*outDir, 0o755)
	start := time.Now()
	var mu sync.Mutex
	var hwAll []L.HW
	var modelAll []L.Model
	if *skipNative {
		hwAll = readJSONL[L.HW](filepath.Join(*outDir, "hw.jsonl"))
	}
	type shard struct{ lo, hi int }
	work := make(chan shard)
	var done atomic.Int64
	var wg sync.WaitGroup
	for j := 0; j < o.jobs; j++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for s := range work {
				cs := cases[s.lo:s.hi]
				var hw []L.HW
				var iwg sync.WaitGroup
				if !*skipNative {
					iwg.Add(1)
					go func() { defer iwg.Done(); hw = runNative(o, cs) }()
				}
				md := runModel(o, cs)
				iwg.Wait()
				mu.Lock()
				hwAll = append(hwAll, hw...)
				modelAll = append(modelAll, md...)
				mu.Unlock()
				n := done.Add(int64(len(cs)))
				fmt.Fprintf(os.Stderr, "\r  %d/%d cases (%s)   ", n, len(cases), time.Since(start).Round(time.Second))
			}
		}()
	}
	for lo := 0; lo < len(cases); lo += o.shard {
		work <- shard{lo, min(lo+o.shard, len(cases))}
	}
	close(work)
	wg.Wait()
	fmt.Fprintln(os.Stderr)
	sort.Slice(hwAll, func(i, j int) bool { return hwAll[i].ID < hwAll[j].ID })
	sort.Slice(modelAll, func(i, j int) bool { return modelAll[i].ID < modelAll[j].ID })
	if !*skipNative {
		writeJSONL(filepath.Join(*outDir, "hw.jsonl"), hwAll)
	}
	writeJSONL(filepath.Join(*outDir, "model.jsonl"), modelAll)
	writeJSONL(filepath.Join(*outDir, "cases.jsonl"), cases)
	verdicts := judge(cases, hwAll, modelAll)
	writeJSONL(filepath.Join(*outDir, "verdicts.jsonl"), verdicts)
	render(*outDir, cases, verdicts, time.Since(start))
}

func judge(cases []L.Case, hw []L.HW, md []L.Model) []Verdict {
	hwBy := map[int]*L.HW{}
	for i := range hw {
		hwBy[hw[i].ID] = &hw[i]
	}
	modelBy := map[int]*L.Model{}
	for i := range md {
		modelBy[md[i].ID] = &md[i]
	}
	asm := map[string]string{}
	verdicts := make([]Verdict, len(cases))
	for i := range cases {
		c := &cases[i]
		verdicts[i] = compareCase(c, hwBy[c.ID], modelBy[c.ID])
		a, ok := asm[c.Bytes]
		if !ok {
			a = disasm(c.Bytes)
			asm[c.Bytes] = a
		}
		verdicts[i].Asm = a
	}
	return verdicts
}

func disasm(h string) string {
	b, err := hex.DecodeString(h)
	if err != nil {
		return "?"
	}
	return gen.Asm(b)
}

func cmdReport(args []string) {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	outDir := fs.String("out", "oracle-out", "output directory of a previous run")
	fs.Parse(args)
	cases := readJSONL[L.Case](filepath.Join(*outDir, "cases.jsonl"))
	verdicts := readJSONL[Verdict](filepath.Join(*outDir, "verdicts.jsonl"))
	render(*outDir, cases, verdicts, 0)
}

func mnemonic(asm string) string {
	if asm == "" {
		return "?"
	}
	f := strings.Fields(asm)
	// skip prefixes printed by GNU syntax
	for len(f) > 1 {
		switch f[0] {
		case "lock", "rep", "repz", "repnz", "repe", "repne", "data16", "addr32", "rex", "rex.W", "cs", "ds", "es", "ss", "fs", "gs":
			f = f[1:]
			continue
		}
		if strings.HasPrefix(f[0], "rex.") || strings.HasPrefix(f[0], "data") {
			f = f[1:]
			continue
		}
		break
	}
	return f[0]
}

func render(outDir string, cases []L.Case, vs []Verdict, took time.Duration) {
	byID := map[int]*L.Case{}
	for i := range cases {
		byID[cases[i].ID] = &cases[i]
	}
	type counts struct{ n, agree, agreeFault, gap, mismatch, unobs, merr int }
	per := map[string]*counts{}
	var tot counts
	gapKinds := map[string]int{}
	unobsKinds := map[string]int{}
	type mkey struct{ class, mnem, kind string }
	mism := map[mkey][]Verdict{}
	mbytes := map[string]bool{}
	for _, v := range vs {
		c := per[v.Class]
		if c == nil {
			c = &counts{}
			per[v.Class] = c
		}
		for _, cc := range []*counts{c, &tot} {
			cc.n++
			switch v.Verdict {
			case Agree:
				cc.agree++
				if strings.HasPrefix(v.Kind, "fault") {
					cc.agreeFault++
				}
			case Gap:
				cc.gap++
			case Mismatch:
				cc.mismatch++
			case Unobserved:
				cc.unobs++
			case ModelError:
				cc.merr++
			}
		}
		switch v.Verdict {
		case Gap:
			gapKinds[v.Kind]++
		case Unobserved:
			unobsKinds[v.Kind]++
		case Mismatch:
			k := mkey{v.Class, mnemonic(v.Asm), v.Kind}
			mism[k] = append(mism[k], v)
			mbytes[v.Bytes] = true
		}
	}
	var b strings.Builder
	fmt.Fprintf(&b, "# Janus amd64 differential oracle: results\n\n")
	if took > 0 {
		fmt.Fprintf(&b, "%d cases in %s.\n\n", len(vs), took.Round(time.Second))
	}
	fmt.Fprintf(&b, "**%d MISMATCH** (soundness: the model succeeded with a result hardware does not produce) "+
		"in %d distinct encodings; %d agree; %d model-gap; %d unobserved; %d model-error.\n\n",
		tot.mismatch, len(mbytes), tot.agree, tot.gap, tot.unobs, tot.merr)
	fmt.Fprintf(&b, "`agree` counts both-succeeded-identically plus both-faulted; the `of which both fault` column is the second part.\n\n")
	fmt.Fprintf(&b, "| class | cases | agree | of which both fault | model-gap | MISMATCH | unobserved | model-error |\n|---|---:|---:|---:|---:|---:|---:|---:|\n")
	classes := make([]string, 0, len(per))
	for k := range per {
		classes = append(classes, k)
	}
	sort.Strings(classes)
	for _, k := range classes {
		c := per[k]
		fmt.Fprintf(&b, "| %s | %d | %d | %d | %d | %d | %d | %d |\n", k, c.n, c.agree, c.agreeFault, c.gap, c.mismatch, c.unobs, c.merr)
	}
	fmt.Fprintf(&b, "| **total** | %d | %d | %d | %d | %d | %d | %d |\n\n", tot.n, tot.agree, tot.agreeFault, tot.gap, tot.mismatch, tot.unobs, tot.merr)

	fmt.Fprintf(&b, "## Model gaps by fault kind\n\n")
	for _, k := range sortedKeys(gapKinds) {
		fmt.Fprintf(&b, "* %s: %d\n", k, gapKinds[k])
	}
	if len(unobsKinds) > 0 {
		fmt.Fprintf(&b, "\n## Unobserved by kind\n\n")
		for _, k := range sortedKeys(unobsKinds) {
			fmt.Fprintf(&b, "* %s: %d\n", k, unobsKinds[k])
		}
	}
	gm := map[string]int{}
	for _, v := range vs {
		if v.Verdict == Gap && v.Kind == "undecodable" {
			gm[mnemonic(v.Asm)]++
		}
	}
	if len(gm) > 0 {
		fmt.Fprintf(&b, "\nUndecodable on the model but executed by hardware, by mnemonic (cases):\n\n")
		var parts []string
		for _, k := range sortedByCount(gm) {
			parts = append(parts, fmt.Sprintf("`%s` %d", k, gm[k]))
		}
		fmt.Fprintf(&b, "%s\n", strings.Join(parts, ", "))
	}

	fmt.Fprintf(&b, "\n## Mismatches\n\n")
	if len(mism) == 0 {
		fmt.Fprintf(&b, "None.\n")
	}
	keys := make([]mkey, 0, len(mism))
	for k := range mism {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(i, j int) bool {
		if len(mism[keys[i]]) != len(mism[keys[j]]) {
			return len(mism[keys[i]]) > len(mism[keys[j]])
		}
		return fmt.Sprint(keys[i]) < fmt.Sprint(keys[j])
	})
	for _, k := range keys {
		ex := mism[k]
		distinct := map[string]bool{}
		for _, v := range ex {
			distinct[v.Bytes] = true
		}
		fmt.Fprintf(&b, "### `%s` — %s — %s: %d cases, %d encodings\n\n", k.mnem, k.class, k.kind, len(ex), len(distinct))
		shown := 0
		seenB := map[string]bool{}
		for _, v := range ex {
			if seenB[v.Bytes] || shown >= 3 {
				continue
			}
			seenB[v.Bytes] = true
			shown++
			fmt.Fprintf(&b, "* case %d: bytes `%s` = `%s`\n", v.ID, v.Bytes, v.Asm)
			for _, d := range v.Diffs {
				fmt.Fprintf(&b, "  * %s\n", d)
			}
			if c := byID[v.ID]; c != nil {
				fmt.Fprintf(&b, "  * input: %s\n", stateSummary(c))
			}
		}
		fmt.Fprintf(&b, "\n")
	}
	os.WriteFile(filepath.Join(outDir, "summary.md"), []byte(b.String()), 0o644)
	fmt.Print(b.String()[:min(len(b.String()), 6000)])
}

// stateSummary prints the registers the instruction names (per x86asm), RSP, flags, seed.
func stateSummary(c *L.Case) string {
	used := map[int]bool{4: true}
	if b, err := hex.DecodeString(c.Bytes); err == nil {
		if inst, ok := gen.Decode(b); ok {
			for _, a := range inst.Args {
				switch a := a.(type) {
				case x86asm.Reg:
					if n, ok := gpr(a); ok {
						used[n] = true
					}
				case x86asm.Mem:
					if n, ok := gpr(a.Base); ok {
						used[n] = true
					}
					if n, ok := gpr(a.Index); ok {
						used[n] = true
					}
				}
			}
		}
	}
	var parts []string
	for r := 0; r < 16; r++ {
		if used[r] {
			parts = append(parts, regNames[r]+"="+c.Regs[r])
		}
	}
	parts = append(parts, "rflags="+flagString(c.RFlags), fmt.Sprintf("seed=%d", c.Seed))
	if len(c.Init) > 0 {
		parts = append(parts, fmt.Sprintf("init=%v", c.Init))
	}
	return strings.Join(parts, " ")
}

func gpr(r x86asm.Reg) (int, bool) {
	switch {
	case r >= x86asm.AL && r <= x86asm.BL:
		return int(r - x86asm.AL), true
	case r >= x86asm.AH && r <= x86asm.BH:
		return int(r - x86asm.AH), true
	case r >= x86asm.SPB && r <= x86asm.R15B:
		return int(r-x86asm.SPB) + 4, true
	case r >= x86asm.AX && r <= x86asm.R15W:
		return int(r - x86asm.AX), true
	case r >= x86asm.EAX && r <= x86asm.R15L:
		return int(r - x86asm.EAX), true
	case r >= x86asm.RAX && r <= x86asm.R15:
		return int(r - x86asm.RAX), true
	}
	return 0, false
}

func sortedKeys(m map[string]int) []string {
	var xs []string
	for k := range m {
		xs = append(xs, k)
	}
	sort.Strings(xs)
	return xs
}

func sortedByCount(m map[string]int) []string {
	xs := sortedKeys(m)
	sort.SliceStable(xs, func(i, j int) bool { return m[xs[i]] > m[xs[j]] })
	return xs
}

func sortStrings(xs []string) { sort.Strings(xs) }
