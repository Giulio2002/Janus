package main

// janus blockers: which extracted words does the trusted Lean decoder reject?
//
// For each symbol, the extraction is computed exactly as `janus extract` would (in memory,
// nothing is written), and every distinct copied word is run through `janus-decode`, a small
// Lean executable that calls `Janus.Arm64.decode` (Janus/Tools/Decode.lean). Because the ISA
// model is trusted, a word it rejects is exactly a word whose execution faults with
// `undecodable`: a function is in the supported subset iff none of its reachable words are
// reported here. (A rejected word only blocks a proof if execution can reach it; e.g. a
// literal pool inside a function would be reported but never executed.)
//
// On amd64 (blockers_amd64.go) the unit is an instruction rather than a word: the extracted
// bytes are swept with x86asm (untrusted, only to find instruction starts) and the bytes from
// each start to the end of its function (at most 15, as Janus.Amd64.Program.fetch returns them)
// are run through Janus.Amd64.decode.

import (
	"bufio"
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

	"golang.org/x/arch/arm64/arm64asm"
)

type blockerSite struct {
	Function string `json:"function"`
	Address  string `json:"address"`
}

type blockerWord struct {
	Word   string        `json:"word"`
	Disasm string        `json:"disasm"`
	Sites  []blockerSite `json:"sites"`
}

type blockerReport struct {
	Symbol        string        `json:"symbol"`
	Error         string        `json:"error,omitempty"`
	Functions     []string      `json:"functions"`
	Stubs         []string      `json:"stubs"`
	Words         int           `json:"words"`
	DistinctWords int           `json:"distinctWords"`
	DataObjects   int           `json:"dataObjects"`
	DataBytes     int           `json:"dataBytes"`
	WritableRefs  []string      `json:"writableRefs"`
	Rejected      []blockerWord `json:"rejected"`
}

type blockersOutput struct {
	Binary       string          `json:"binary"`
	BinarySha256 string          `json:"binarySha256"`
	Decoder      string          `json:"decoder"`
	MaxFunctions int             `json:"maxFunctions"`
	Symbols      []blockerReport `json:"symbols"`
}

func disasm(w uint32) string {
	var buf [4]byte
	buf[0], buf[1], buf[2], buf[3] = byte(w), byte(w>>8), byte(w>>16), byte(w>>24)
	inst, err := arm64asm.Decode(buf[:])
	if err != nil {
		return "?"
	}
	return arm64asm.GNUSyntax(inst)
}

// leanDecode runs janus-decode on words and returns which ones Lean accepts.
func leanDecode(exe string, words []uint32) (map[uint32]bool, error) {
	var in bytes.Buffer
	for _, w := range words {
		fmt.Fprintf(&in, "0x%x\n", w)
	}
	cmd := exec.Command(exe)
	cmd.Stdin = &in
	var out, errb bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &errb
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("%s: %v\n%s%s", exe, err, out.String(), errb.String())
	}
	res := map[uint32]bool{}
	sc := bufio.NewScanner(&out)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		f := strings.Fields(sc.Text())
		if len(f) < 2 || (f[1] != "ok" && f[1] != "none") {
			return nil, fmt.Errorf("unexpected janus-decode output line %q", sc.Text())
		}
		v, err := strconv.ParseUint(f[0], 0, 32)
		if err != nil {
			return nil, fmt.Errorf("unexpected janus-decode output line %q", sc.Text())
		}
		res[uint32(v)] = f[1] == "ok"
	}
	for _, w := range words {
		if _, ok := res[w]; !ok {
			return nil, fmt.Errorf("janus-decode gave no answer for 0x%x", w)
		}
	}
	return res, nil
}

func cmdBlockers(args []string, stdout, stderr io.Writer) error {
	pos, opts, err := parseArgs(args, "max-functions", "janus-root", "json", "contract")
	if err != nil {
		return usageErr("%v", err)
	}
	if len(pos) < 2 {
		return usageErr("blockers takes <binary> <symbol>...")
	}
	maxF := defaultMaxFunctions
	if v, ok := opts["max-functions"]; ok {
		if maxF, err = strconv.Atoi(v); err != nil || maxF < 1 {
			return usageErr("--max-functions needs a positive integer, got %q", v)
		}
	}
	b, err := loadBinary(pos[0])
	if err != nil {
		return err
	}
	root, err := findJanusRoot(opts["janus-root"])
	if err != nil {
		return err
	}
	lake, err := findLake()
	if err != nil {
		return err
	}
	lr := &leanRunner{lake: lake, root: root}
	if out, err := lr.run("build", "janus-decode"); err != nil {
		return &diag{Msg: "lake build janus-decode failed in " + displayPath(root), Stage: "Lean decoder build",
			Next: "Fix the Lean build (lake build janus-decode), then rerun.", Details: out}
	}
	exe := filepath.Join(root, ".lake", "build", "bin", "janus-decode")
	if b.GOARCH == "amd64" {
		return blockersAmd64(b, pos[1:], maxF, exe, opts["json"], stdout)
	}

	type site struct {
		fn string
		pc uint64
	}
	var reports []blockerReport
	sites := map[int]map[uint32][]site{} // report index -> word -> sites
	all := map[uint32]bool{}
	for _, sym := range pos[1:] {
		r := blockerReport{Symbol: sym, Functions: []string{}, Stubs: []string{}, WritableRefs: []string{}, Rejected: []blockerWord{}}
		x, err := extractWith(b, sym, maxF, optsList(opts, "contract"))
		if err != nil {
			r.Error = strings.TrimSuffix(strings.SplitN(err.Error(), "\n", 2)[0], ":")
			reports = append(reports, r)
			continue
		}
		ws := map[uint32][]site{}
		for _, s := range x.Segments {
			r.Functions = append(r.Functions, s.Name)
			for i, w := range s.Words {
				ws[w] = append(ws[w], site{s.Name, s.Base + 4*uint64(i)})
				all[w] = true
				r.Words++
			}
		}
		for _, s := range x.Stubs {
			r.Stubs = append(r.Stubs, s.Name)
		}
		for _, d := range x.Data {
			r.DataObjects++
			r.DataBytes += len(d.Bytes)
		}
		seen := map[string]bool{}
		for _, s := range x.Skipped {
			if s.Reason == "writable" && !seen[s.Symbol+s.Section] {
				seen[s.Symbol+s.Section] = true
				r.WritableRefs = append(r.WritableRefs, fmt.Sprintf("%s (%s)", s.Symbol, s.Section))
			}
		}
		r.DistinctWords = len(ws)
		sites[len(reports)] = ws
		reports = append(reports, r)
	}
	var words []uint32
	for w := range all {
		words = append(words, w)
	}
	sort.Slice(words, func(i, j int) bool { return words[i] < words[j] })
	ok, err := leanDecode(exe, words)
	if err != nil {
		return &diag{Msg: "janus-decode failed: " + err.Error(), Stage: "Lean decoding",
			Next: "Rebuild with lake build janus-decode and rerun."}
	}

	nOK, nBlocked, nFailed := 0, 0, 0
	for i := range reports {
		r := &reports[i]
		if r.Error != "" {
			nFailed++
			fmt.Fprintf(stdout, "%s: extraction failed: %s\n", r.Symbol, r.Error)
			continue
		}
		for w, ss := range sites[i] {
			if ok[w] {
				continue
			}
			sort.Slice(ss, func(a, c int) bool { return ss[a].pc < ss[c].pc })
			bw := blockerWord{Word: fmt.Sprintf("0x%08x", w), Disasm: disasm(w)}
			for _, s := range ss {
				bw.Sites = append(bw.Sites, blockerSite{s.fn, hex0x(s.pc)})
			}
			r.Rejected = append(r.Rejected, bw)
		}
		first := func(bw blockerWord) uint64 { v, _ := strconv.ParseUint(bw.Sites[0].Address, 0, 64); return v }
		sort.Slice(r.Rejected, func(a, c int) bool { return first(r.Rejected[a]) < first(r.Rejected[c]) })
		status := "all decoded"
		if len(r.Rejected) > 0 {
			status = fmt.Sprintf("%d rejected word(s)", len(r.Rejected))
			nBlocked++
		} else {
			nOK++
		}
		fmt.Fprintf(stdout, "%s: %d function(s), %d word(s) (%d distinct), %d data object(s): %s\n",
			r.Symbol, len(r.Functions), r.Words, r.DistinctWords, r.DataObjects, status)
		for _, bw := range r.Rejected {
			more := ""
			if len(bw.Sites) > 1 {
				more = fmt.Sprintf(" (+%d more site(s))", len(bw.Sites)-1)
			}
			fmt.Fprintf(stdout, "  %s  %-10s  %-36s %s%s\n", bw.Sites[0].Address, bw.Word, bw.Disasm, bw.Sites[0].Function, more)
		}
		if len(r.WritableRefs) > 0 {
			fmt.Fprintf(stdout, "  writable data referenced (not copied): %s\n", strings.Join(r.WritableRefs, ", "))
		}
	}
	fmt.Fprintf(stdout, "Summary: %d symbol(s): %d fully decoded, %d with rejected words, %d extraction failed (decoder: Janus.Arm64.decode via janus-decode, %d distinct words).\n",
		len(reports), nOK, nBlocked, nFailed, len(words))
	if p := opts["json"]; p != "" {
		o := blockersOutput{Binary: displayPath(b.Path), BinarySha256: b.Sha256, Decoder: "Janus.Arm64.decode (janus-decode)",
			MaxFunctions: maxF, Symbols: reports}
		buf, _ := json.MarshalIndent(o, "", "  ")
		if err := os.WriteFile(p, append(buf, '\n'), 0o644); err != nil {
			return &diag{Msg: fmt.Sprintf("Cannot write %s: %v", p, err), Stage: "writing report"}
		}
	}
	return nil
}
