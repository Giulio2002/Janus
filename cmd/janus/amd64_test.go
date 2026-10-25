package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"sync"
	"testing"
)

var (
	amd64Once sync.Once
	amd64Bin  string
	amd64Err  error
)

// exampleAmd64 builds examples/basic for linux/amd64 (once per test run).
func exampleAmd64(t *testing.T) string {
	t.Helper()
	amd64Once.Do(func() {
		dir, err := os.MkdirTemp("", "janus-test-amd64-")
		if err != nil {
			amd64Err = err
			return
		}
		amd64Bin = filepath.Join(dir, "examples-amd64")
		cmd := exec.Command("go", "build", "-trimpath", "-o", amd64Bin, "./cmd")
		cmd.Dir = filepath.Join(repoRoot, "examples", "basic")
		cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64", "GOAMD64=v1", "CGO_ENABLED=0")
		if out, err := cmd.CombinedOutput(); err != nil {
			amd64Err = fmt.Errorf("building amd64 example binary: %v\n%s", err, out)
		}
	})
	if amd64Err != nil {
		t.Fatal(amd64Err)
	}
	return amd64Bin
}

func extractAmd64Example(t *testing.T, sym string) (*Extraction, string) {
	t.Helper()
	bin := exampleAmd64(t)
	dir := filepath.Join(t.TempDir(), "art")
	code, _, stderr := runJanus(t, "extract", bin, sym, dir)
	if code != 0 {
		t.Fatalf("extract %s failed: %s", sym, stderr)
	}
	x, err := extract(bin, sym, defaultMaxFunctions)
	if err != nil {
		t.Fatal(err)
	}
	return x, dir
}

func TestAmd64BranchAndDataSynthetic(t *testing.T) {
	const base = 0x1000
	code := []byte{
		0xe8, 0x00, 0x00, 0x00, 0x00, // 0x1000 call 0x1005
		0x74, 0xfe, // 0x1005 je 0x1005
		0x0f, 0x84, 0x10, 0x00, 0x00, 0x00, // 0x1007 je 0x101d
		0xe9, 0xf0, 0xff, 0xff, 0xff, // 0x100d jmp 0x1002
		0x48, 0x8d, 0x05, 0x20, 0x00, 0x00, 0x00, // 0x1012 lea rax, [rip+0x20] -> 0x1039
		0x48, 0x8b, 0x0d, 0x08, 0x00, 0x00, 0x00, // 0x1019 mov rcx, [rip+8] -> 0x1028
		0x48, 0x8b, 0x04, 0xc8, // 0x1020 mov rax, [rax+rcx*8] (not a fixed address)
		0xff, 0xd0, // 0x1024 call rax (indirect: no target)
		0xc3, // 0x1026 ret
	}
	insts := sweepAmd64(code, base)
	var got []string
	for _, in := range insts {
		if tg, ok := amd64BranchTarget(in); ok {
			got = append(got, fmt.Sprintf("%x->%x", in.PC, tg))
		}
	}
	want := []string{"1000->1005", "1005->1005", "1007->101d", "100d->1002"}
	if strings.Join(got, " ") != strings.Join(want, " ") {
		t.Errorf("branch targets %v, want %v", got, want)
	}
	refs := amd64DataRefs(insts)
	wantRefs := []DataRef{{From: 0x1012, Target: 0x1039, Kind: "rip-lea"}, {From: 0x1019, Target: 0x1028, Kind: "rip-mem"}}
	if fmt.Sprint(refs) != fmt.Sprint(wantRefs) {
		t.Errorf("data refs %v, want %v", refs, wantRefs)
	}
	// Undecodable bytes are skipped one at a time and do not hide later instructions.
	insts = sweepAmd64([]byte{0x0f, 0xff, 0xff, 0xeb, 0x00}, base)
	if n := len(insts); n == 0 {
		t.Fatal("no instructions decoded")
	}
	last := insts[len(insts)-1]
	if tg, ok := amd64BranchTarget(last); !ok || tg != base+5 {
		t.Errorf("last instruction %v at %x: target %x %v", last.Inst, last.PC, tg, ok)
	}
}

func TestAmd64ExtractAdd(t *testing.T) {
	x, dir := extractAmd64Example(t, "example.com/basic.Add")
	if len(x.Segments) != 1 || !bytes.Equal(x.Segments[0].Bytes, []byte{0x48, 0x01, 0xd8, 0xc3}) || len(x.Segments[0].Words) != 0 {
		t.Fatalf("Add segment: %+v", x.Segments)
	}
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if !bytes.Equal(lean, x.Lean) {
		t.Fatal("written Extracted.lean differs from the extraction")
	}
	base := x.Segments[0].Base
	for _, s := range []string{
		"import Janus\n",
		"(example.com/basic, go1.26.0, linux/amd64).\n",
		"namespace Extracted\nopen Janus\n",
		fmt.Sprintf("def segments : List Amd64.Segment := [\n  { name := \"example.com/basic.Add\", base := 0x%x, bytes := [0x48, 0x01, 0xd8, 0xc3] } ]\n", base),
		"def stubs : List Stub := []\n",
		"def exitAddr : Nat := 0\n",
		"def program : Amd64.Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }\n",
		fmt.Sprintf("def entry : Nat := 0x%x\n", base),
		"end Extracted\n",
	} {
		if !strings.Contains(string(lean), s) {
			t.Errorf("Extracted.lean lacks %q:\n%s", s, lean)
		}
	}
	id := readIdentity(t, dir)
	if id.GOARCH != "amd64" || id.GOAMD64 != "v1" || id.GOOS != "linux" || len(id.Functions) != 1 ||
		id.Functions[0].Bytes != 4 || id.Functions[0].Words != 0 || id.Size != 4 {
		t.Errorf("identity: %+v", id)
	}
	// The byte copy agrees with the binary, as objdump reads it, for every example function.
	for _, f := range exampleFuncs {
		x, _ := extractAmd64Example(t, "example.com/basic."+f)
		for _, s := range x.Segments {
			if got := objdumpAmd64Bytes(t, exampleAmd64(t), s.Base, s.Base+s.Size); !bytes.Equal(got, s.Bytes) {
				t.Errorf("%s: segment %s bytes differ from objdump:\n  got  %x\n  want %x", f, s.Name, s.Bytes, got)
			}
		}
	}
}

// objdumpAmd64Bytes returns the bytes of [start, stop) as printed by objdump -d.
func objdumpAmd64Bytes(t *testing.T, bin string, start, stop uint64) []byte {
	t.Helper()
	if _, err := exec.LookPath("objdump"); err != nil {
		t.Skip("objdump not installed")
	}
	out, err := exec.Command("objdump", "-d", "-z", fmt.Sprintf("--start-address=0x%x", start),
		fmt.Sprintf("--stop-address=0x%x", stop), bin).Output()
	if err != nil {
		t.Fatalf("objdump: %v", err)
	}
	line := regexp.MustCompile(`^\s*([0-9a-f]+):\t((?:[0-9a-f]{2} )+)`)
	var res []byte
	for _, l := range strings.Split(string(out), "\n") {
		m := line.FindStringSubmatch(l)
		if m == nil {
			continue
		}
		b, err := hex.DecodeString(strings.ReplaceAll(m[2], " ", ""))
		if err != nil {
			t.Fatal(err)
		}
		res = append(res, b...)
	}
	return res
}

func TestAmd64CalleesAndStubs(t *testing.T) {
	x, _ := extractAmd64Example(t, "example.com/basic.AddThree")
	if len(x.Segments) != 2 || x.Segments[0].Name != "example.com/basic.AddThree" || x.Segments[1].Name != "example.com/basic.Add" {
		t.Fatalf("AddThree segments: %v", segNames(x))
	}
	if len(x.Stubs) != 1 || x.Stubs[0].Kind != stubMorestack || !strings.HasPrefix(x.Stubs[0].Name, "runtime.morestack") {
		t.Errorf("AddThree stubs: %+v", x.Stubs)
	}
	for sym, stub := range map[string]string{"Get": "runtime.panicBounds", "Div": "runtime.panicdivide"} {
		x, _ := extractAmd64Example(t, "example.com/basic."+sym)
		if len(x.Segments) != 1 || len(x.Stubs) != 1 || x.Stubs[0].Name != stub || x.Stubs[0].Kind != stubPanic {
			t.Errorf("%s: segments %v stubs %+v", sym, segNames(x), x.Stubs)
		}
		if !strings.Contains(string(x.Lean), fmt.Sprintf("{ name := %q, addr := 0x%x, kind := .panic }", stub, x.Stubs[0].Addr)) {
			t.Errorf("%s: stub not rendered:\n%s", sym, x.Lean)
		}
	}
}

func segNames(x *Extraction) []string {
	var n []string
	for _, s := range x.Segments {
		n = append(n, s.Name)
	}
	return n
}

func TestAmd64Data(t *testing.T) {
	x, _ := extractAmd64Example(t, "example.com/basic.Table")
	want := make([]byte, 0, 64)
	for _, v := range []uint64{0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
		0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917} {
		want = binary.LittleEndian.AppendUint64(want, v)
	}
	found := false
	for _, d := range x.Data {
		if bytes.Contains(d.Bytes, want) && d.Section == ".rodata" {
			found = true
		}
	}
	if !found {
		t.Errorf("Table: constant table not copied: %+v", x.Data)
	}
	if !strings.Contains(string(x.Lean), "def program : Amd64.Program :=\n  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }\n") ||
		!strings.Contains(string(x.Lean), "def data : List DataSegment := [") {
		t.Errorf("Table: data not rendered:\n%s", x.Lean)
	}
	for _, f := range []string{"GlobalTable", "Bump"} {
		x, _ := extractAmd64Example(t, "example.com/basic."+f)
		if len(x.Data) != 0 || len(x.Skipped) == 0 || x.Skipped[0].Reason != "writable" {
			t.Errorf("%s: data %+v skipped %+v", f, x.Data, x.Skipped)
		}
	}
}

func TestAmd64CheckAndTamper(t *testing.T) {
	_, dir := extractAmd64Example(t, "example.com/basic.Add256")
	if code, out, stderr := runJanus(t, "check", dir); code != 0 || !strings.Contains(out, "Valid:") || !strings.Contains(out, "linux/amd64") {
		t.Fatalf("check failed (%d): %s%s", code, out, stderr)
	}
	p := filepath.Join(dir, "Extracted.lean")
	lean, _ := os.ReadFile(p)
	if err := os.WriteFile(p, bytes.Replace(lean, []byte("0x48"), []byte("0x49"), 1), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 1 || !strings.Contains(stderr, "Invalid:") {
		t.Fatalf("tampered Extracted.lean accepted (%d): %s", code, stderr)
	}
}

func TestAmd64List(t *testing.T) {
	code, out, stderr := runJanus(t, "list", exampleAmd64(t), "--filter", "example.com/basic.Add256")
	if code != 0 || !strings.Contains(out, "linux/amd64") || !strings.Contains(out, "example.com/basic.Add256") {
		t.Fatalf("list (%d): %s%s", code, out, stderr)
	}
}

func TestAmd64Blockers(t *testing.T) {
	code, out, stderr := runJanus(t, "blockers", exampleAmd64(t), "example.com/basic.Add", "example.com/basic.AddThree",
		"--janus-root", repoRoot)
	if code != 0 || !strings.Contains(out, "example.com/basic.Add: 1 function(s)") ||
		!strings.Contains(out, "all decoded") || !strings.Contains(out, "Janus.Amd64.decode") {
		t.Fatalf("blockers on amd64 (%d): %s%s", code, out, stderr)
	}
}

// Binaries for other architectures are still rejected.
func TestRejects386(t *testing.T) {
	bin := filepath.Join(t.TempDir(), "examples-386")
	cmd := exec.Command("go", "build", "-trimpath", "-o", bin, "./cmd")
	cmd.Dir = filepath.Join(repoRoot, "examples", "basic")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=386", "CGO_ENABLED=0")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("building 386 binary: %v\n%s", err, out)
	}
	code, _, stderr := runJanus(t, "list", bin)
	if code != 1 || !strings.Contains(stderr, "Stage: binary validation") {
		t.Fatalf("386 binary accepted (%d): %s", code, stderr)
	}
}

// The amd64 additions to identity.json are omitted for arm64, so arm64 output is unchanged.
func TestArm64IdentityUnchanged(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.AddThree")
	raw, _ := os.ReadFile(filepath.Join(dir, "identity.json"))
	for _, k := range []string{`"bytes"`, `"goamd64"`} {
		if bytes.Contains(raw, []byte(k)) {
			t.Errorf("arm64 identity.json contains %s:\n%s", k, raw)
		}
	}
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if bytes.Contains(lean, []byte("Amd64")) || !bytes.Contains(lean, []byte("def program : Program := ")) {
		t.Errorf("arm64 Extracted.lean changed shape:\n%s", lean)
	}
}

// TestSweepAmd64EVEX: EVEX (which x86asm does not decode) and the VEX opmask instructions are
// swept with their real lengths, and a RIP-relative EVEX load is a data reference (WP-G).
func TestSweepAmd64EVEX(t *testing.T) {
	code := []byte{
		0x62, 0xf1, 0xfe, 0x48, 0x6f, 0x05, 0x10, 0x00, 0x00, 0x00, // VMOVDQU64 0x10(%rip), Z0
		0x62, 0xf2, 0x7d, 0xc9, 0x8d, 0xc4, // VPERMB Z4, Z0, K1, Z0 {z}
		0x62, 0xf3, 0xd5, 0x48, 0xce, 0xdb, 0x00, // VGF2P8AFFINEQB $0, Z3, Z5, Z3
		0xc4, 0xe1, 0xfb, 0x92, 0xc8, // KMOVQ AX, K1
		0xc3, // RET
	}
	insts := sweepAmd64(code, 0x1000)
	var lens []int
	for _, in := range insts {
		lens = append(lens, in.Inst.Len)
	}
	if want := []int{10, 6, 7, 5, 1}; fmt.Sprint(lens) != fmt.Sprint(want) {
		t.Fatalf("lengths %v, want %v", lens, want)
	}
	refs := amd64DataRefs(insts)
	if len(refs) != 1 || refs[0].From != 0x1000 || refs[0].Target != 0x1000+10+0x10 {
		t.Fatalf("data references %+v, want one from 0x1000 to 0x101a", refs)
	}
}
