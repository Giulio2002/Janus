package main

import (
	"bufio"
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

func TestDataRefsSynthetic(t *testing.T) {
	const pc = 0xaa73c
	// adrp x27, 0xe2000; add x27, x27, #0xb40; ldp x3, x4, [x27]
	ws := []uint32{0x900001db, 0x912d037b, 0xa9401363}
	refs := dataRefs(ws, pc)
	want := []DataRef{{pc + 4, 0xe2b40, "adrp+add"}, {pc + 8, 0xe2b40, "adrp+ldst"}}
	if fmt.Sprint(refs) != fmt.Sprint(want) {
		t.Errorf("adrp+add+ldp: got %v, want %v", refs, want)
	}
	// adrp x27, 0xe2000; ldr x0, [x27, #16]  (ADRP+LDR, no ADD)
	if refs := dataRefs([]uint32{0x900001db, 0xf9400b60}, pc); len(refs) != 1 || refs[0].Target != 0xe2010 || refs[0].Kind != "adrp+ldst" {
		t.Errorf("adrp+ldr: got %v", refs)
	}
	// adrp x27; mov x27, x0 (clobbers); add x27, x27, #0xb40: no reference.
	if refs := dataRefs([]uint32{0x900001db, 0xaa0003fb, 0x912d037b}, pc); len(refs) != 0 {
		t.Errorf("clobbered register still tracked: %v", refs)
	}
	// adrp x27; bl (call clobbers); add: no reference.
	if refs := dataRefs([]uint32{0x900001db, 0x94000010, 0x912d037b}, pc); len(refs) != 0 {
		t.Errorf("call did not clear tracking: %v", refs)
	}
	// ldr x0, #8 (literal) and adr x1, #16.
	refs = dataRefs([]uint32{0x58000040, 0x10000081}, 0x1000)
	want = []DataRef{{0x1000, 0x1008, "ldr-literal"}, {0x1004, 0x1014, "adr"}}
	if fmt.Sprint(refs) != fmt.Sprint(want) {
		t.Errorf("literal/adr: got %v, want %v", refs, want)
	}
}

// objdumpAdrpTargets returns the targets of ADRP+ADD and ADRP+LDR/LDP pairs (adjacent, same
// register) in [start, stop), as disassembled by objdump.
func objdumpAdrpTargets(t *testing.T, bin string, start, stop uint64) map[uint64]bool {
	t.Helper()
	tool, err := exec.LookPath("aarch64-linux-gnu-objdump")
	if err != nil {
		t.Skip("aarch64-linux-gnu-objdump not installed")
	}
	out, err := exec.Command(tool, "-d", fmt.Sprintf("--start-address=0x%x", start), fmt.Sprintf("--stop-address=0x%x", stop), bin).Output()
	if err != nil {
		t.Fatal(err)
	}
	adrp := regexp.MustCompile(`\tadrp\t(x\d+), ([0-9a-f]+)`)
	add := regexp.MustCompile(`\tadd\t(x\d+), (x\d+), #0x([0-9a-f]+)$`)
	ld := regexp.MustCompile(`\tld[a-z]*\t.*\[(x\d+)(?:, #(-?\d+))?\]`)
	targets := map[uint64]bool{}
	var reg string
	var page uint64
	sc := bufio.NewScanner(bytes.NewReader(out))
	for sc.Scan() {
		l := sc.Text()
		if g := adrp.FindStringSubmatch(l); g != nil {
			reg = g[1]
			page, _ = strconv.ParseUint(g[2], 16, 64)
			continue
		}
		if reg != "" {
			if g := add.FindStringSubmatch(l); g != nil && g[2] == reg {
				v, _ := strconv.ParseUint(g[3], 16, 64)
				targets[page+v] = true
			} else if g := ld.FindStringSubmatch(l); g != nil && g[1] == reg {
				v, _ := strconv.ParseInt(g[2], 10, 64)
				targets[uint64(int64(page)+v)] = true
			}
		}
		reg = ""
	}
	return targets
}

// objdumpBytes returns the bytes of [start, stop) from objdump -s. Each output line holds the
// 16 bytes from its address (fewer on the last line) as hex groups aligned to 4-byte
// boundaries, so an unaligned start gives a short first group; the ASCII column follows.
func objdumpBytes(t *testing.T, bin string, start, stop uint64) []byte {
	t.Helper()
	out, err := exec.Command("aarch64-linux-gnu-objdump", "-s", fmt.Sprintf("--start-address=0x%x", start),
		fmt.Sprintf("--stop-address=0x%x", stop), bin).Output()
	if err != nil {
		t.Fatal(err)
	}
	line := regexp.MustCompile(`^ ([0-9a-f]+) (.*)$`)
	group := regexp.MustCompile(`^(?:[0-9a-f]{2}){1,4}$`)
	var res []byte
	sc := bufio.NewScanner(bytes.NewReader(out))
	for sc.Scan() {
		g := line.FindStringSubmatch(sc.Text())
		if g == nil {
			continue
		}
		addr, _ := strconv.ParseUint(g[1], 16, 64)
		if addr != start+uint64(len(res)) {
			t.Fatalf("objdump -s line at %#x, expected %#x", addr, start+uint64(len(res)))
		}
		want := int(min(16, stop-addr))
		n := 0
		for _, chunk := range strings.Fields(g[2]) {
			if n == want {
				break
			}
			if !group.MatchString(chunk) || n+len(chunk)/2 > want {
				t.Fatalf("objdump -s line at %#x: unexpected group %q", addr, chunk)
			}
			for i := 0; i < len(chunk); i += 2 {
				v, _ := strconv.ParseUint(chunk[i:i+2], 16, 8)
				res = append(res, byte(v))
			}
			n += len(chunk) / 2
		}
		if n != want {
			t.Fatalf("objdump -s line at %#x has %d bytes, want %d", addr, n, want)
		}
	}
	if uint64(len(res)) != stop-start {
		t.Fatalf("objdump -s gave %d bytes for [%#x, %#x)", len(res), start, stop)
	}
	return res
}

// needObjdump skips the test when aarch64-linux-gnu-objdump is not installed.
func needObjdump(t *testing.T) {
	t.Helper()
	if _, err := exec.LookPath("aarch64-linux-gnu-objdump"); err != nil {
		t.Skip("aarch64-linux-gnu-objdump not installed")
	}
}

// checkDataAgainstObjdump checks an extraction's data against objdump: every ADRP pair objdump
// shows in the entry function is detected and either copied (read-only) or reported as
// skipped, and every copied object lies in a read-only data section with exactly the bytes
// objdump -s shows there.
func checkDataAgainstObjdump(t *testing.T, b *Binary, bin string, x *Extraction) {
	t.Helper()
	sym := x.Entry.Name
	covered := func(a uint64) bool {
		for _, d := range x.Data {
			if a >= d.Base && a < d.Base+uint64(len(d.Bytes)) {
				return true
			}
		}
		return false
	}
	skipped := map[uint64]string{}
	for _, s := range x.Skipped {
		skipped[s.Target] = s.Reason
	}
	detected := map[uint64]bool{}
	for _, r := range x.DataRefs {
		detected[r.Target] = true
	}
	e := x.Segments[0]
	objTargets := objdumpAdrpTargets(t, bin, e.Base, e.Base+e.Size)
	if len(objTargets) == 0 {
		t.Errorf("%s: objdump shows no ADRP references", sym)
	}
	for a := range objTargets {
		sec, _ := b.sectionOf(a)
		if !detected[a] {
			t.Errorf("%s: objdump reference to %#x (%s) not detected", sym, a, sec.Name)
		}
		if !covered(a) && skipped[a] == "" {
			t.Errorf("%s: objdump reference to %#x (%s) neither copied nor reported", sym, a, sec.Name)
		}
	}
	for _, d := range x.Data {
		sec, ok := b.sectionOf(d.Base)
		if !ok || sec.Writable || sec.Exec || sec.Name == ".gopclntab" || d.Base+uint64(len(d.Bytes)) > sec.End() || d.Section != sec.Name {
			t.Errorf("%s: data %s at %#x is not inside a read-only data section (%s)", sym, d.Name, d.Base, sec.Name)
		}
		if got := objdumpBytes(t, bin, d.Base, d.Base+uint64(len(d.Bytes))); !bytes.Equal(got, d.Bytes) {
			t.Errorf("%s: data %s bytes differ from objdump:\n%x\n%x", sym, d.Name, d.Bytes, got)
		}
	}
}

func le64s(vs ...uint64) []byte {
	var out []byte
	for _, v := range vs {
		for i := 0; i < 8; i++ {
			out = append(out, byte(v>>(8*i)))
		}
	}
	return out
}

// The read-only data examples: Table (an [8]uint64 literal), HexDigit (a string constant) and
// SetOne256 (the 32-byte constant 1), all in .rodata and addressed with ADRP+ADD (then LDP or a
// register-indexed load).
func TestDataReadOnlyExamples(t *testing.T) {
	needObjdump(t)
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	table := le64s(0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
		0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917)
	one := append([]byte{1}, make([]byte, 31)...)
	cases := []struct {
		fn     string
		prefix []byte // the constant the function loads, at the start of the first object
		size   int    // exact size of the single copied object, or 0 to only require the prefix
		ldst   bool   // an ADRP+ADD address is also used by an LDP [Xn, #imm]
	}{
		{"Table", table, 0, true},
		{"HexDigit", []byte("0123456789abcdef"), 0, false},
		{"SetOne256", one, 32, true},
	}
	for _, c := range cases {
		sym := "example.com/basic." + c.fn
		x, err := extractFrom(b, sym, defaultMaxFunctions)
		if err != nil {
			t.Fatalf("%s: %v", sym, err)
		}
		if len(x.Data) != 1 || len(x.Skipped) != 0 {
			t.Fatalf("%s: want one data object and nothing skipped, got %+v / %+v", sym, x.Data, x.Skipped)
		}
		d := x.Data[0]
		if d.Section != ".rodata" || !bytes.HasPrefix(d.Bytes, c.prefix) || (c.size != 0 && len(d.Bytes) != c.size) {
			t.Errorf("%s: data %s (%s) is %x, want prefix %x", sym, d.Name, d.Section, d.Bytes, c.prefix)
		}
		kinds := map[string]bool{}
		for _, r := range x.DataRefs {
			kinds[r.Kind] = true
			if r.Target < d.Base || r.Target >= d.Base+uint64(len(d.Bytes)) {
				t.Errorf("%s: reference %+v outside the copied object", sym, r)
			}
		}
		if !kinds["adrp+add"] || kinds["adrp+ldst"] != c.ldst {
			t.Errorf("%s: reference kinds %v", sym, kinds)
		}
		checkDataAgainstObjdump(t, b, exampleBin, x)
		lean := string(x.Lean)
		if !strings.Contains(lean, "def data : List DataSegment := [\n  { name := ") ||
			!strings.Contains(lean, "def program : Program :=\n  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }\n") {
			t.Errorf("%s: unexpected Lean data shape:\n%s", sym, lean)
		}
	}
}

// Writable globals are reported, never copied: GlobalTable reads an initialised var
// (.noptrdata, ADRP+ADD), Bump reads and writes a zero-initialised one (.noptrbss, ADRP+LDR/STR).
func TestDataWritableExamples(t *testing.T) {
	needObjdump(t)
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	cases := []struct {
		fn, global, section, kind string
		refs                      int
	}{
		{"GlobalTable", "example.com/basic.tbl", ".noptrdata", "adrp+add", 1},
		{"Bump", "example.com/basic.counter", ".noptrbss", "adrp+ldst", 2},
	}
	for _, c := range cases {
		sym := "example.com/basic." + c.fn
		x, err := extractFrom(b, sym, defaultMaxFunctions)
		if err != nil {
			t.Fatalf("%s: %v", sym, err)
		}
		if len(x.Data) != 0 {
			t.Errorf("%s: writable data copied: %+v", sym, x.Data)
		}
		if len(x.Skipped) != c.refs {
			t.Errorf("%s: want %d skipped reference(s), got %+v", sym, c.refs, x.Skipped)
		}
		for _, s := range x.Skipped {
			if s.Reason != "writable" || s.Section != c.section || s.Symbol != c.global || s.Kind != c.kind {
				t.Errorf("%s: unexpected skipped reference %+v", sym, s)
			}
		}
		checkDataAgainstObjdump(t, b, exampleBin, x)
		if strings.Contains(string(x.Lean), "def data") {
			t.Errorf("%s: Lean has data although nothing was copied", sym)
		}
		code, out, stderr := runJanus(t, "extract", exampleBin, sym, filepath.Join(t.TempDir(), c.fn))
		if code != 0 || !strings.Contains(out, "0 data object(s) (0 bytes)") ||
			!strings.Contains(stderr, "references 0x") || !strings.Contains(stderr, "("+c.global+") in writable section "+c.section) {
			t.Errorf("%s: extract %d\n%s\n%s", sym, code, out, stderr)
		}
	}
}

func TestDataCheckTamper(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "one")
	code, out, stderr := runJanus(t, "extract", exampleBin, "example.com/basic.SetOne256", dir)
	if code != 0 || !strings.Contains(out, "1 data object(s) (32 bytes)") || !strings.Contains(out, "  data  0x") {
		t.Fatalf("extract: %d %s %s", code, out, stderr)
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check: %s", stderr)
	}
	id := readIdentity(t, dir)
	if len(id.Data) != 1 || id.Data[0].Size != 32 || id.Data[0].Section != ".rodata" || len(id.DataRefs) == 0 {
		t.Errorf("identity data: %+v %+v", id.Data, id.DataRefs)
	}
	// Change the constant 1 into 2 in both Extracted.lean and its recorded hash.
	leanPath, idPath := filepath.Join(dir, "Extracted.lean"), filepath.Join(dir, "identity.json")
	orig, _ := os.ReadFile(leanPath)
	origID, _ := os.ReadFile(idPath)
	forged := bytes.Replace(orig, []byte("bytes := [\n      0x01,"), []byte("bytes := [\n      0x02,"), 1)
	if bytes.Equal(forged, orig) {
		t.Fatalf("test pattern not found in:\n%s", orig)
	}
	os.WriteFile(leanPath, forged, 0o644)
	os.WriteFile(idPath, bytes.Replace(origID, []byte(sha256Hex(orig)), []byte(sha256Hex(forged)), 1), 0o644)
	code, _, stderr = runJanus(t, "check", dir)
	if code != 1 || !strings.Contains(stderr, "differs from the regenerated extraction") {
		t.Fatalf("forged data accepted: %d %s", code, stderr)
	}
	// Dropping a data record from identity.json is caught too.
	os.WriteFile(leanPath, orig, 0o644)
	os.WriteFile(idPath, regexp.MustCompile(`(?s)"data": \[.*?\]`).ReplaceAll(origID, []byte(`"data": []`)), 0o644)
	code, _, stderr = runJanus(t, "check", dir)
	if code != 1 || !strings.Contains(stderr, "differs from the regenerated identity") {
		t.Fatalf("edited identity data accepted: %d %s", code, stderr)
	}
}

// TestDataLarge covers the large-data rendering: main.main of the example binary reaches about
// 400 runtime functions that reference some 80 read-only objects (about 40 KB), so every object
// becomes its own `def data<i>`, those over 1024 bytes with a raised maxRecDepth. The objects
// are cross-checked against objdump, `check` accepts the artifacts and rejects an edited byte,
// and (without -short) the file elaborates and a proof about `data` verifies.
func TestDataLarge(t *testing.T) {
	t.Parallel()
	needObjdump(t)
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	x, err := extractFrom(b, "main.main", 1000)
	if err != nil {
		t.Fatal(err)
	}
	total, big := 0, 0
	for _, d := range x.Data {
		total += len(d.Bytes)
		if len(d.Bytes) > segmentWordLimit {
			big++
		}
	}
	if len(x.Data) < 40 || total < 16*1024 || big == 0 {
		t.Fatalf("main.main data: %d object(s), %d bytes, %d over %d bytes; want a large case", len(x.Data), total, big, segmentWordLimit)
	}
	checkDataAgainstObjdump(t, b, exampleBin, x)
	for i := 1; i < len(x.Data); i++ {
		if p := x.Data[i-1]; p.Base+uint64(len(p.Bytes)) >= x.Data[i].Base && p.Section == x.Data[i].Section {
			t.Errorf("objects %s and %s overlap or touch (not merged)", p.Name, x.Data[i].Name)
		}
	}
	lean := string(x.Lean)
	if strings.Contains(lean, "def data : List DataSegment := [\n  {") ||
		!strings.Contains(lean, "def data : List DataSegment := [\n  data0, data1, data2,") ||
		!strings.Contains(lean, fmt.Sprintf("def data%d : DataSegment :=\n  { name := ", len(x.Data)-1)) ||
		strings.Contains(lean, fmt.Sprintf("def data%d :", len(x.Data))) {
		t.Errorf("unexpected large data shape")
	}
	if n := strings.Count(lean, "set_option maxRecDepth 100000 in\ndef data"); n != big {
		t.Errorf("%d data definitions raise maxRecDepth, want %d", n, big)
	}

	dir := filepath.Join(t.TempDir(), "main")
	code, out, stderr := runJanus(t, "extract", exampleBin, "main.main", dir, "--max-functions", "1000")
	if code != 0 || !strings.Contains(out, fmt.Sprintf("%d data object(s) (%d bytes)", len(x.Data), total)) {
		t.Fatalf("extract: %d %s %s", code, out, stderr)
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check: %s", stderr)
	}
	if id := readIdentity(t, dir); len(id.Data) != len(x.Data) || len(id.SkippedData) == 0 {
		t.Errorf("identity: %d data record(s), %d skipped", len(id.Data), len(id.SkippedData))
	}
	if !testing.Short() {
		if _, err := findLake(); err == nil {
			proof := filepath.Join(t.TempDir(), "Proof.lean")
			os.WriteFile(proof, []byte(fmt.Sprintf("import Extracted\nnamespace Proof\n"+
				"theorem correctness : Extracted.program.data.length = %d := by decide\nend Proof\n", len(x.Data))), 0o644)
			code, out, stderr := runJanus(t, "verify", dir, "--proof", proof, "--janus-root", repoRoot)
			if code != 0 || !strings.HasPrefix(out, "Verified: Proof.correctness\n") {
				t.Fatalf("verify: %d\n%s\n%s", code, out, stderr)
			}
		}
	}
	// An edited byte in one of the large objects (with the hash updated) is rejected.
	leanPath, idPath := filepath.Join(dir, "Extracted.lean"), filepath.Join(dir, "identity.json")
	orig, _ := os.ReadFile(leanPath)
	origID, _ := os.ReadFile(idPath)
	i := strings.LastIndex(string(orig), "set_option maxRecDepth 100000 in\ndef data")
	j := i + regexp.MustCompile(`0x[0-9a-f]{2}`).FindStringIndex(string(orig[i:]))[0]
	forged := append([]byte(nil), orig...)
	if forged[j+3] = '0'; orig[j+3] == '0' { // change the low hex digit of the first byte
		forged[j+3] = '1'
	}
	os.WriteFile(leanPath, forged, 0o644)
	os.WriteFile(idPath, bytes.Replace(origID, []byte(sha256Hex(orig)), []byte(sha256Hex(forged)), 1), 0o644)
	if code, _, stderr := runJanus(t, "check", dir); code != 1 || !strings.Contains(stderr, "differs from the regenerated extraction") {
		t.Fatalf("forged large data accepted: %d %s", code, stderr)
	}
}

// TestBlockers runs the Lean decoder; it needs lake.
func TestBlockers(t *testing.T) {
	if testing.Short() {
		t.Skip("runs Lean")
	}
	if _, err := findLake(); err != nil {
		t.Skip("lake not installed")
	}
	jsonOut := filepath.Join(t.TempDir(), "b.json")
	code, out, stderr := runJanus(t, "blockers", exampleBin, "example.com/basic.Get", "example.com/basic.AddThree",
		"example.com/basic.Nope", "--janus-root", repoRoot, "--json", jsonOut)
	if code != 0 {
		t.Fatalf("blockers: %d %s %s", code, out, stderr)
	}
	for _, s := range []string{"example.com/basic.Get: 1 function(s)", "all decoded", "example.com/basic.Nope: extraction failed",
		"Summary: 3 symbol(s): 2 fully decoded, 0 with rejected words, 1 extraction failed"} {
		if !strings.Contains(out, s) {
			t.Errorf("blockers output lacks %q:\n%s", s, out)
		}
	}
	if _, err := os.Stat(jsonOut); err != nil {
		t.Error(err)
	}
	// The decoder itself: a floating-point word (FADD D0, D1, D2; Advanced SIMD is decoded since
	// the SIMD merge, FP arithmetic is not) is rejected, ADD and RET are accepted.
	root, release, _ := findJanusRoot(repoRoot, "janus-decode")
	defer release()
	ok, err := leanDecode(filepath.Join(root, ".lake", "build", "bin", "janus-decode"), []uint32{0x8b010000, 0xd65f03c0, 0x1e622820})
	if err != nil {
		t.Fatal(err)
	}
	if !ok[0x8b010000] || !ok[0xd65f03c0] || ok[0x1e622820] {
		t.Errorf("janus-decode verdicts: %v", ok)
	}
}
