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
	"sync"
	"testing"
)

var (
	u256Once sync.Once
	u256Path string
	u256Err  error
)

// uint256Bin returns the uint256 target binary: the one built by targets/uint256/build.sh,
// or a fresh build of the same module (needs the module cache or network).
func uint256Bin(t *testing.T) string {
	t.Helper()
	u256Once.Do(func() {
		p := filepath.Join(repoRoot, "targets", "uint256", "bin", "uint256-arm64")
		if _, err := os.Stat(p); err == nil {
			u256Path = p
			return
		}
		dir, err := os.MkdirTemp("", "janus-u256-")
		if err != nil {
			u256Err = err
			return
		}
		u256Path = filepath.Join(dir, "uint256-arm64")
		cmd := exec.Command("go", "build", "-trimpath", "-buildvcs=false", "-o", u256Path, ".")
		cmd.Dir = filepath.Join(repoRoot, "targets", "uint256")
		cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=arm64", "CGO_ENABLED=0")
		if out, err := cmd.CombinedOutput(); err != nil {
			u256Err = fmt.Errorf("%v\n%s", err, out)
		}
	})
	if u256Err != nil {
		t.Skipf("cannot build the uint256 target: %v", u256Err)
	}
	return u256Path
}

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

// objdumpBytes returns the bytes of [start, stop) from objdump -s.
func objdumpBytes(t *testing.T, bin string, start, stop uint64) []byte {
	t.Helper()
	out, err := exec.Command("aarch64-linux-gnu-objdump", "-s", fmt.Sprintf("--start-address=0x%x", start),
		fmt.Sprintf("--stop-address=0x%x", stop), bin).Output()
	if err != nil {
		t.Fatal(err)
	}
	line := regexp.MustCompile(`^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?){1,4})`)
	var res []byte
	sc := bufio.NewScanner(bytes.NewReader(out))
	for sc.Scan() {
		g := line.FindStringSubmatch(sc.Text())
		if g == nil {
			continue
		}
		for _, chunk := range strings.Fields(g[2]) {
			for i := 0; i+2 <= len(chunk); i += 2 {
				v, _ := strconv.ParseUint(chunk[i:i+2], 16, 8)
				res = append(res, byte(v))
			}
		}
	}
	return res
}

func TestDataUint256ExpAddMod(t *testing.T) {
	bin := uint256Bin(t)
	b, err := loadBinary(bin)
	if err != nil {
		t.Fatal(err)
	}
	for _, m := range []string{"Exp", "AddMod"} {
		sym := "github.com/holiman/uint256.(*Int)." + m
		x, err := extractFrom(b, sym, defaultMaxFunctions)
		if err != nil {
			t.Fatalf("%s: %v", sym, err)
		}
		if len(x.Data) == 0 {
			t.Fatalf("%s: no data extracted", sym)
		}
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
		// Every ADRP pair objdump shows in the entry function is either copied (read-only)
		// or reported as skipped.
		e := x.Segments[0]
		objTargets := objdumpAdrpTargets(t, bin, e.Base, e.Base+e.Size)
		if len(objTargets) == 0 {
			t.Errorf("%s: objdump shows no ADRP references", sym)
		}
		for a := range objTargets {
			sec, _ := b.sectionOf(a)
			if !covered(a) && skipped[a] == "" {
				t.Errorf("%s: objdump reference to %#x (%s) neither copied nor reported", sym, a, sec.Name)
			}
		}
		for _, d := range x.Data {
			sec, ok := b.sectionOf(d.Base)
			if !ok || sec.Writable || sec.Exec || sec.Name == ".gopclntab" || d.Base+uint64(len(d.Bytes)) > sec.End() {
				t.Errorf("%s: data %s at %#x is not inside a read-only data section (%s)", sym, d.Name, d.Base, sec.Name)
			}
			if got := objdumpBytes(t, bin, d.Base, d.Base+uint64(len(d.Bytes))); !bytes.Equal(got, d.Bytes) {
				t.Errorf("%s: data %s bytes differ from objdump:\n%x\n%x", sym, d.Name, d.Bytes, got)
			}
		}
		lean := string(x.Lean)
		if !strings.Contains(lean, "def data : List DataSegment := [\n  { name := ") ||
			!strings.Contains(lean, "def program : Program :=\n  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }\n") {
			t.Errorf("%s: unexpected Lean data shape:\n%s", sym, lean)
		}
	}
	// Exp starts from the constant 1 (res := Int{1, 0, 0, 0}), loaded from .rodata.
	x, _ := extractFrom(b, "github.com/holiman/uint256.(*Int).Exp", defaultMaxFunctions)
	one := append([]byte{1}, make([]byte, 31)...)
	if !bytes.Equal(x.Data[0].Bytes[:32], one) {
		t.Errorf("Exp data is %x, want the uint256 constant 1", x.Data[0].Bytes)
	}
	// AddMod reaches math/bits.Div64, whose panic path takes the address of
	// runtime.divideError/overflowError in .data: reported as writable, never copied.
	x, _ = extractFrom(b, "github.com/holiman/uint256.(*Int).AddMod", defaultMaxFunctions)
	found := false
	for _, s := range x.Skipped {
		if s.Reason == "writable" && s.Section == ".data" && strings.HasPrefix(s.Symbol, "runtime.") {
			found = true
		}
	}
	if !found {
		t.Errorf("AddMod: expected a writable .data reference to be reported, got %+v", x.Skipped)
	}
}

func TestDataCheckTamper(t *testing.T) {
	bin := uint256Bin(t)
	dir := filepath.Join(t.TempDir(), "exp")
	code, out, stderr := runJanus(t, "extract", bin, "github.com/holiman/uint256.(*Int).Exp", dir)
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
	// The decoder itself: a SIMD word is rejected, ADD and RET are accepted.
	root, _ := findJanusRoot(repoRoot)
	ok, err := leanDecode(filepath.Join(root, ".lake", "build", "bin", "janus-decode"), []uint32{0x8b010000, 0xd65f03c0, 0x4cdf2c00})
	if err != nil {
		t.Fatal(err)
	}
	if !ok[0x8b010000] || !ok[0xd65f03c0] || ok[0x4cdf2c00] {
		t.Errorf("janus-decode verdicts: %v", ok)
	}
}
