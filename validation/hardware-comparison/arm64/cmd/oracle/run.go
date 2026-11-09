package main

import (
	"bufio"
	"bytes"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

type runOpts struct {
	qemu, runner, model string
	jobs, shard         int
}

// pipeThrough runs cmd with the cases on stdin and decodes one T per output line.
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

// runNative runs cases through the native runner, restarting it after the case it died on
// (the runner catches every fault of the instruction itself, so this only happens on harness
// bugs).
func runNative(o runOpts, cases []L.Case) []L.HW {
	var res []L.HW
	argv := []string{o.runner}
	if o.qemu != "" {
		argv = []string{o.qemu, o.runner}
	}
	for len(cases) > 0 {
		out, stderr, err := pipeThrough[L.HW](argv, []string{"GODEBUG=asyncpreemptoff=1"}, cases)
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

func runModel(o runOpts, cases []L.Case) []L.Model {
	out, stderr, err := pipeThrough[L.Model]([]string{o.model}, nil, cases)
	if len(out) < len(cases) {
		fmt.Fprintf(os.Stderr, "oracle: janus-oracle produced %d/%d results (%v): %s\n", len(out), len(cases), err, stderr)
	}
	return out
}

func cmdRun(args []string) {
	fs := flag.NewFlagSet("run", flag.ExitOnError)
	casesF := fs.String("cases", "", "comma-separated case files")
	outDir := fs.String("out", "oracle-out", "output directory")
	var o runOpts
	fs.StringVar(&o.qemu, "qemu", "/usr/bin/qemu-aarch64", "qemu-aarch64 (empty: run the runner directly, on arm64 hosts)")
	fs.StringVar(&o.runner, "runner", "oracle/bin/runner", "native runner (GOARCH=arm64)")
	fs.StringVar(&o.model, "model", ".lake/build/bin/janus-oracle", "janus-oracle executable")
	fs.IntVar(&o.jobs, "j", 16, "parallel shards")
	fs.IntVar(&o.shard, "shard", 2000, "cases per shard")
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

	hwBy := map[int]*L.HW{}
	modelBy := map[int]*L.Model{}
	var mu sync.Mutex
	var hwAll []L.HW
	var modelAll []L.Model
	if *skipNative {
		for _, h := range readJSONL[L.HW](filepath.Join(*outDir, "hw.jsonl")) {
			hwAll = append(hwAll, h)
		}
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
				var md []L.Model
				var iwg sync.WaitGroup
				if !*skipNative {
					iwg.Add(1)
					go func() { defer iwg.Done(); hw = runNative(o, cs) }()
				}
				md = runModel(o, cs)
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
	for i := range hwAll {
		hwBy[hwAll[i].ID] = &hwAll[i]
	}
	for i := range modelAll {
		modelBy[modelAll[i].ID] = &modelAll[i]
	}
	asm := disasm(cases)
	verdicts := make([]Verdict, len(cases))
	for i := range cases {
		verdicts[i] = compareCase(&cases[i], hwBy[cases[i].ID], modelBy[cases[i].ID])
		verdicts[i].Asm = asm[cases[i].Word]
	}
	writeJSONL(filepath.Join(*outDir, "verdicts.jsonl"), verdicts)
	render(*outDir, cases, verdicts, time.Since(start))
}

func cmdReport(args []string) {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	outDir := fs.String("out", "oracle-out", "output directory of a previous run")
	fs.Parse(args)
	cases := readJSONL[L.Case](filepath.Join(*outDir, "cases.jsonl"))
	verdicts := readJSONL[Verdict](filepath.Join(*outDir, "verdicts.jsonl"))
	render(*outDir, cases, verdicts, 0)
}

var objdumpLine = regexp.MustCompile(`^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(.*)$`)

// disasm returns binutils' disassembly of every distinct word (for the report only; the
// comparison never depends on it).
func disasm(cases []L.Case) map[string]string {
	idx := map[string]int{}
	var words []string
	for _, c := range cases {
		if _, ok := idx[c.Word]; !ok {
			idx[c.Word] = len(words)
			words = append(words, c.Word)
		}
	}
	buf := make([]byte, 4*len(words))
	for i, w := range words {
		binary.LittleEndian.PutUint32(buf[4*i:], uint32(hexv(w)))
	}
	tmp, err := os.CreateTemp("", "oracle-words-*.bin")
	if err != nil {
		return nil
	}
	defer os.Remove(tmp.Name())
	tmp.Write(buf)
	tmp.Close()
	out, err := exec.Command("aarch64-linux-gnu-objdump", "-D", "-b", "binary", "-maarch64", "-z", tmp.Name()).Output()
	res := map[string]string{}
	if err != nil {
		return res
	}
	for _, line := range strings.Split(string(out), "\n") {
		m := objdumpLine.FindStringSubmatch(line)
		if m == nil {
			continue
		}
		off, _ := strconv.ParseUint(m[1], 16, 64)
		if int(off/4) < len(words) {
			s := strings.Join(strings.Fields(strings.SplitN(m[2], "//", 2)[0]), " ")
			res[words[off/4]] = s
		}
	}
	return res
}

func mnemonic(asm string) string {
	if asm == "" {
		return "?"
	}
	return strings.Fields(asm)[0]
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
	type mkey struct{ class, mnem, kind string }
	mism := map[mkey][]Verdict{}
	mwords := map[string]bool{}
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
		case Mismatch:
			k := mkey{v.Class, mnemonic(v.Asm), v.Kind}
			mism[k] = append(mism[k], v)
			mwords[v.Word] = true
		}
	}
	var b strings.Builder
	fmt.Fprintf(&b, "# Janus differential oracle: results\n\n")
	if took > 0 {
		fmt.Fprintf(&b, "%d cases in %s.\n\n", len(vs), took.Round(time.Second))
	}
	fmt.Fprintf(&b, "**%d MISMATCH** (soundness: the model succeeded with a result hardware does not produce) "+
		"in %d distinct words; %d agree; %d model-gap; %d unobserved; %d model-error.\n\n",
		tot.mismatch, len(mwords), tot.agree, tot.gap, tot.unobs, tot.merr)
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
	// Gap mnemonics: which instructions the model does not cover yet.
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
		words := map[string]bool{}
		for _, v := range ex {
			words[v.Word] = true
		}
		fmt.Fprintf(&b, "### `%s` — %s — %s: %d cases, %d words\n\n", k.mnem, k.class, k.kind, len(ex), len(words))
		shown := 0
		seenW := map[string]bool{}
		for _, v := range ex {
			if seenW[v.Word] || shown >= 3 {
				continue
			}
			seenW[v.Word] = true
			shown++
			c := byID[v.ID]
			fmt.Fprintf(&b, "* case %d: word `%s` = `%s`\n", v.ID, v.Word, v.Asm)
			for _, d := range v.Diffs {
				fmt.Fprintf(&b, "  * %s\n", d)
			}
			if c != nil {
				fmt.Fprintf(&b, "  * input: %s\n", stateSummary(c, v.Word))
			}
		}
		fmt.Fprintf(&b, "\n")
	}
	os.WriteFile(filepath.Join(outDir, "summary.md"), []byte(b.String()), 0o644)
	fmt.Print(b.String()[:min(len(b.String()), 6000)])
}

// stateSummary prints the operand registers of a case (fields Rd/Rn/Rm/Ra/Rt2/Rs), SP,
// NZCV and seed.
func stateSummary(c *L.Case, word string) string {
	w := uint32(hexv(word))
	regs := map[int]bool{int(w & 31): true, int(w >> 5 & 31): true, int(w >> 10 & 31): true, int(w >> 16 & 31): true}
	var parts []string
	for _, r := range sortedInts(regs) {
		if r < 31 {
			parts = append(parts, fmt.Sprintf("x%d=%s", r, c.X[r]))
		}
	}
	parts = append(parts, "sp="+c.SP, fmt.Sprintf("nzcv=%04b", c.NZCV), fmt.Sprintf("seed=%d", c.Seed))
	return strings.Join(parts, " ")
}

func sortedInts(m map[int]bool) []int {
	var xs []int
	for k := range m {
		xs = append(xs, k)
	}
	sort.Ints(xs)
	return xs
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
