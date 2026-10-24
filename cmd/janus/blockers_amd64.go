package main

// janus blockers on amd64: which extracted instructions does the trusted Lean decoder reject?
//
// The extraction is computed exactly as `janus extract` would. Each function's bytes are swept
// linearly with x86asm (untrusted: it only proposes instruction starts), and for every start
// the bytes from there to the end of the function, at most 15, are run through
// `Janus.Amd64.decode` (`janus-decode`, `x86 <bytes>` queries). An instruction is reported
// when Lean rejects it, or when Lean decodes a different length than x86asm (then the two
// disagree about where the next instruction starts, and the sweep after it is not reliable).
// INT3 (0xCC) padding is skipped: the Lean decoder rejects it on purpose and Go and C
// compilers only use it between functions.

import (
	"bufio"
	"bytes"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"os/exec"
	"sort"
	"strconv"
	"strings"

	"golang.org/x/arch/x86/x86asm"
)

// leanDecodeX86 runs janus-decode on byte strings and returns, for each, the decoded length
// (0 when Lean rejects it).
func leanDecodeX86(exe string, queries []string) (map[string]int, error) {
	var in bytes.Buffer
	for _, q := range queries {
		fmt.Fprintf(&in, "x86 %s\n", q)
	}
	cmd := exec.Command(exe)
	cmd.Stdin = &in
	var out, errb bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &errb
	if err := cmd.Run(); err != nil {
		return nil, fmt.Errorf("%s: %v\n%s%s", exe, err, out.String(), errb.String())
	}
	res := map[string]int{}
	sc := bufio.NewScanner(&out)
	sc.Buffer(make([]byte, 1<<20), 1<<24)
	for sc.Scan() {
		f := strings.Fields(sc.Text())
		if len(f) < 3 || f[0] != "x86" || (f[2] != "ok" && f[2] != "none") {
			return nil, fmt.Errorf("unexpected janus-decode output line %q", sc.Text())
		}
		n := 0
		if f[2] == "ok" {
			if len(f) < 4 {
				return nil, fmt.Errorf("unexpected janus-decode output line %q", sc.Text())
			}
			v, err := strconv.Atoi(f[3])
			if err != nil || v < 1 {
				return nil, fmt.Errorf("unexpected janus-decode output line %q", sc.Text())
			}
			n = v
		}
		res[f[1]] = n
	}
	for _, q := range queries {
		if _, ok := res[q]; !ok {
			return nil, fmt.Errorf("janus-decode gave no answer for x86 %s", q)
		}
	}
	return res, nil
}

func blockersAmd64(b *Binary, syms []string, maxF int, exe, jsonPath string, stdout io.Writer) error {
	type inst struct {
		fn     string
		pc     uint64
		query  string // hex of the fetched bytes
		x86len int
		disasm string
		key    string // the instruction's own bytes, for grouping
	}
	var reports []blockerReport
	insts := map[int][]inst{}
	all := map[string]bool{}
	for _, sym := range syms {
		r := blockerReport{Symbol: sym, Functions: []string{}, Stubs: []string{}, WritableRefs: []string{}, Rejected: []blockerWord{}}
		x, err := extractFrom(b, sym, maxF)
		if err != nil {
			r.Error = strings.TrimSuffix(strings.SplitN(err.Error(), "\n", 2)[0], ":")
			reports = append(reports, r)
			continue
		}
		distinct := map[string]bool{}
		var is []inst
		for _, s := range x.Segments {
			r.Functions = append(r.Functions, s.Name)
			for _, in := range sweepAmd64(s.Bytes, s.Base) {
				if in.Inst.Op == x86asm.INT && in.Inst.Len == 1 { // INT3 (0xCC) padding
					continue
				}
				off := int(in.PC - s.Base)
				end := off + 15
				if end > len(s.Bytes) {
					end = len(s.Bytes)
				}
				q := hex.EncodeToString(s.Bytes[off:end])
				key := hex.EncodeToString(s.Bytes[off : off+in.Inst.Len])
				dis := x86asm.GNUSyntax(in.Inst, in.PC, nil)
				if key == "f30f1efa" {
					dis = "endbr64"
				}
				is = append(is, inst{fn: s.Name, pc: in.PC, query: q, x86len: in.Inst.Len, disasm: dis, key: key})
				all[q] = true
				distinct[key] = true
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
		r.DistinctWords = len(distinct)
		insts[len(reports)] = is
		reports = append(reports, r)
	}
	var queries []string
	for q := range all {
		queries = append(queries, q)
	}
	sort.Strings(queries)
	lens, err := leanDecodeX86(exe, queries)
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
		byKey := map[string]int{} // instruction bytes -> index in r.Rejected
		for _, in := range insts[i] {
			n := lens[in.query]
			if n == in.x86len {
				continue
			}
			what := in.disasm
			if n != 0 {
				what = fmt.Sprintf("%s (Lean decodes %d bytes, x86asm %d)", in.disasm, n, in.x86len)
			}
			site := blockerSite{in.fn, hex0x(in.pc)}
			if j, ok := byKey[in.key]; ok {
				r.Rejected[j].Sites = append(r.Rejected[j].Sites, site)
				continue
			}
			byKey[in.key] = len(r.Rejected)
			r.Rejected = append(r.Rejected, blockerWord{Word: in.key, Disasm: what, Sites: []blockerSite{site}})
		}
		status := "all decoded"
		if len(r.Rejected) > 0 {
			status = fmt.Sprintf("%d rejected instruction(s)", len(r.Rejected))
			nBlocked++
		} else {
			nOK++
		}
		fmt.Fprintf(stdout, "%s: %d function(s), %d instruction(s) (%d distinct), %d data object(s): %s\n",
			r.Symbol, len(r.Functions), r.Words, r.DistinctWords, r.DataObjects, status)
		for _, bw := range r.Rejected {
			more := ""
			if len(bw.Sites) > 1 {
				more = fmt.Sprintf(" (+%d more site(s))", len(bw.Sites)-1)
			}
			fmt.Fprintf(stdout, "  %s  %-20s  %-36s %s%s\n", bw.Sites[0].Address, bw.Word, bw.Disasm, bw.Sites[0].Function, more)
		}
		if len(r.WritableRefs) > 0 {
			fmt.Fprintf(stdout, "  writable data referenced (not copied): %s\n", strings.Join(r.WritableRefs, ", "))
		}
	}
	fmt.Fprintf(stdout, "Summary: %d symbol(s): %d fully decoded, %d with rejected instructions, %d extraction failed (decoder: Janus.Amd64.decode via janus-decode, %d distinct fetches).\n",
		len(reports), nOK, nBlocked, nFailed, len(queries))
	if jsonPath != "" {
		o := blockersOutput{Binary: displayPath(b.Path), BinarySha256: b.Sha256, Decoder: "Janus.Amd64.decode (janus-decode)",
			MaxFunctions: maxF, Symbols: reports}
		buf, _ := json.MarshalIndent(o, "", "  ")
		if err := os.WriteFile(jsonPath, append(buf, '\n'), 0o644); err != nil {
			return &diag{Msg: fmt.Sprintf("Cannot write %s: %v", jsonPath, err), Stage: "writing report"}
		}
	}
	return nil
}
