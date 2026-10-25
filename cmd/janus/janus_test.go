package main

import (
	"bufio"
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strconv"
	"strings"
	"testing"
)

var (
	repoRoot   string
	exampleBin string
)

var exampleFuncs = []string{"Add", "Max", "Add128", "Mul64", "Sum", "Get", "Add256", "Div", "AddThree",
	"Table", "HexDigit", "SetOne256", "GlobalTable", "Bump"}

// testCacheDir is the janus cache every test uses (JANUS_CACHE_DIR, set for the whole test
// process by TestMain): the framework is built there once across test runs, and the tests never
// touch the user's own cache. It is $JANUS_TEST_CACHE_DIR if set, else <user cache
// dir>/janus-test (~/.cache/janus-test, next to but separate from ~/.cache/janus), or
// /var/tmp/janus-test-cache-<uid> if that is unavailable or on a RAM filesystem. Never
// os.TempDir(): /tmp is a tmpfs on many hosts, and the cache (framework and JanusASL builds,
// one workspace per consumer test) is tens of GB of RAM there. The cache collector
// (cachegc.go) bounds it like any other cache.
func testCacheDir() string { return resolveTestCacheDir(os.Getenv("JANUS_TEST_CACHE_DIR")) }

func resolveTestCacheDir(env string) string {
	if env != "" {
		if abs, err := filepath.Abs(env); err == nil {
			return abs
		}
		return env
	}
	if d, err := os.UserCacheDir(); err == nil && filepath.IsAbs(d) {
		if fsi := statFSExisting(d); !fsi.ram {
			return filepath.Join(d, "janus-test")
		}
	}
	return filepath.Join("/var/tmp", fmt.Sprintf("janus-test-cache-%d", os.Geteuid()))
}

// statFSExisting is statFS of p or of its nearest existing ancestor.
func statFSExisting(p string) fsInfo {
	for {
		if _, err := os.Stat(p); err == nil || p == filepath.Dir(p) {
			return statFS(p)
		}
		p = filepath.Dir(p)
	}
}

// defaultTestParallel is the -parallel default for this package (unless -parallel is given):
// min(GOMAXPROCS / 4, (MemAvailable - 40 GiB) / 20 GiB, 2), at least 1, the budget of
// scripts/lib/parallel.sh (a test that verifies can hold ~20 GB: a cold kernel replay of the
// framework, the proof's Lean process and the auditor).
func defaultTestParallel() int {
	n := runtime.GOMAXPROCS(0) / 4
	if n > 2 {
		n = 2 // at most 2 heavy jobs at once on a shared host
	}
	if b, err := os.ReadFile("/proc/meminfo"); err == nil {
		for _, line := range strings.Split(string(b), "\n") {
			if f := strings.Fields(line); len(f) >= 2 && f[0] == "MemAvailable:" {
				if kb, err := strconv.Atoi(f[1]); err == nil {
					if m := (kb - 40*1024*1024) / (20 * 1024 * 1024); m < n {
						n = m
					}
				}
			}
		}
	}
	if n < 1 {
		n = 1
	}
	return n
}

func TestMain(m *testing.M) {
	flag.Parse()
	// Build the example binaries with the same pinned Go release as scripts/build-examples*.sh.
	if os.Getenv("GOTOOLCHAIN") == "" {
		os.Setenv("GOTOOLCHAIN", "go1.26.0")
	}
	// The test cache and no JANUS_ROOT for the whole process (useTestCache then has nothing to
	// change, so tests that use it can run in parallel).
	os.Setenv("JANUS_CACHE_DIR", testCacheDir())
	os.Setenv("JANUS_ROOT", "")
	explicit := false
	flag.Visit(func(f *flag.Flag) { explicit = explicit || f.Name == "test.parallel" })
	if !explicit {
		_ = flag.Set("test.parallel", strconv.Itoa(defaultTestParallel()))
	}
	wd, _ := os.Getwd()
	repoRoot = filepath.Clean(filepath.Join(wd, "..", ".."))
	dir, err := os.MkdirTemp("", "janus-test-")
	if err != nil {
		panic(err)
	}
	exampleBin = filepath.Join(dir, "examples-arm64")
	cmd := exec.Command("go", "build", "-trimpath", "-o", exampleBin, "./cmd")
	cmd.Dir = filepath.Join(repoRoot, "examples", "basic")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=arm64", "CGO_ENABLED=0")
	if out, err := cmd.CombinedOutput(); err != nil {
		fmt.Fprintf(os.Stderr, "building example binary: %v\n%s", err, out)
		os.Exit(1)
	}
	code := m.Run()
	os.RemoveAll(dir)
	os.Exit(code)
}

func runJanus(t *testing.T, args ...string) (int, string, string) {
	t.Helper()
	var out, errb bytes.Buffer
	code := run(args, &out, &errb)
	return code, out.String(), errb.String()
}

func mustExtract(t *testing.T, sym string, extra ...string) string {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "art")
	code, _, stderr := runJanus(t, append([]string{"extract", exampleBin, sym, dir}, extra...)...)
	if code != 0 {
		t.Fatalf("extract %s failed: %s", sym, stderr)
	}
	return dir
}

func readIdentity(t *testing.T, dir string) *Identity {
	t.Helper()
	b, err := os.ReadFile(filepath.Join(dir, "identity.json"))
	if err != nil {
		t.Fatal(err)
	}
	var id Identity
	if err := json.Unmarshal(b, &id); err != nil {
		t.Fatal(err)
	}
	return &id
}

func TestBranchTarget(t *testing.T) {
	cases := []struct {
		w      uint32
		pc, to uint64
		call   bool
	}{
		{0x97ffd35f, 0x93174, 0x87ef0, true},  // bl runtime.panicBounds
		{0x97ffcae6, 0x93188, 0x85d20, true},  // bl runtime.morestack_noctxt
		{0x17ffffeb, 0x93194, 0x93140, false}, // b (backwards)
		{0x14000004, 0x9311c, 0x9312c, false}, // b (forwards)
		{0x54000042, 0x930d4, 0x930dc, false}, // b.cs
		{0x54ffff8c, 0x93130, 0x93120, false}, // b.gt (backwards)
		{0xb40000a1, 0x93208, 0x9321c, false}, // cbz x1
		{0xb5000041, 0x1000, 0x1008, false},   // cbnz x1, +8
		{0x36080040, 0x1000, 0x1008, false},   // tbz w0, #1, +8
		{0xb7ffffe0, 0x1000, 0xffc, false},    // tbnz x0, #63, -4
	}
	for _, c := range cases {
		got, ok := branchTarget(c.w, c.pc)
		if !ok || got != c.to {
			t.Errorf("branchTarget(%#08x, %#x) = %#x, %v; want %#x", c.w, c.pc, got, ok, c.to)
		}
		if isCall(c.w) != c.call {
			t.Errorf("isCall(%#08x) = %v", c.w, !c.call)
		}
	}
	for _, w := range []uint32{0x8b010000, 0xd65f03c0, 0xd61f0200 /* br x16 */, 0xd63f0200 /* blr x16 */, 0} {
		if _, ok := branchTarget(w, 0x1000); ok {
			t.Errorf("branchTarget(%#08x) should not be a direct branch", w)
		}
	}
}

func TestStubKind(t *testing.T) {
	cases := map[string]StubKind{
		"runtime.panicBounds": stubPanic, "runtime.panicdivide": stubPanic, "runtime.panicBounds64": stubPanic,
		"runtime.panicshift": stubPanic, "runtime.panicmem": stubPanic, "runtime.gopanic": stubPanic,
		"runtime.panicwrap": stubPanic, "runtime.goPanicIndex": stubPanic, "runtime.goPanicSliceAlen": stubPanic,
		"runtime.morestack.abi0": stubMorestack, "runtime.morestack_noctxt.abi0": stubMorestack,
	}
	for name, want := range cases {
		if got, ok := stubKind(name); !ok || got != want {
			t.Errorf("stubKind(%q) = %q, %v; want %q", name, got, ok, want)
		}
	}
	// Round 6 F3: an import path that starts with "runtime.panic" or "runtime.morestack" is not
	// package runtime (docs/AUDIT-ROUND6.md).
	for _, name := range []string{"runtime.mallocgc", "example.com/basic.Add", "main.panicky",
		"runtime.panicky/lib.Zero", "runtime.panicky/lib.Zero.abi0", "runtime.morestacks.io/x.F",
		"runtime.gopanic/x.F", "runtime%2epanicky.F",
		// Round 7 G1: exact go1.26 names only. Not runtime functions of go1.26 (an assembly
		// function or a //go:linkname push of another package can take such a name), the other
		// ABI of a listed one (linked under a mangled name), and runtime functions that return
		// (panicCheck1/2) or throw (morestackc).
		"runtime.panicJanusR7", "runtime.morestackJanusR7", "runtime.panicIndex", "runtime.panicSliceAlen",
		"runtime.panicdivide.abi0", "runtime.gopanic.abi0", "runtime.morestack_noctxt", "runtime.morestack",
		"runtime.panicCheck1", "runtime.panicCheck2", "runtime.morestackc", "runtime.morestackc.abi0",
		"runtime.panicdivide.abiinternal"} {
		if _, ok := stubKind(name); ok {
			t.Errorf("%s classified as a stub", name)
		}
	}
}

// Round 7 G1: a listed stub name is trusted only in a binary with an ELF symbol table, when no
// other function has the same name. Round 8 G3: and only when its code is the runtime's
// (stubpin_test.go has the content cases on real binaries); the Go version is not read.
func TestClassifyStub(t *testing.T) {
	g := Func{Name: "runtime.panicdivide", Addr: 0x1000, Size: 16}
	mk := func(src, ver string, funcs ...Func) *Binary {
		return &Binary{Path: "bin", SymbolSource: src, GoVersion: ver, GOARCH: "arm64", Funcs: funcs}
	}
	for _, b := range []*Binary{
		mk("pclntab", "go1.26.0", g),
		mk("symtab", "go1.26.0", g, Func{Name: "runtime.panicdivide", Addr: 0x2000, Size: 16}),
		mk("symtab", "go1.26.0", g), // no code: cannot match the pin
		mk("symtab", "go1.27.0", g),
	} {
		if _, ok, err := b.classifyStub(g); err == nil || ok {
			t.Errorf("%s %s %d funcs: classified (ok=%v err=%v)", b.SymbolSource, b.GoVersion, len(b.Funcs), ok, err)
		}
	}
	// pclntab names carry no ABI suffix: an unlisted name that looks like a stub is an error
	h := Func{Name: "runtime.morestack_noctxt", Addr: 0x3000, Size: 16}
	if _, ok, err := mk("pclntab", "go1.26.0", h).classifyStub(h); err == nil || ok {
		t.Errorf("pclntab morestack_noctxt: ok=%v err=%v", ok, err)
	}
	// an ordinary function is code
	f := Func{Name: "runtime.panicJanusR7", Addr: 0x4000, Size: 16}
	if _, ok, err := mk("symtab", "go1.26.0", f).classifyStub(f); err != nil || ok {
		t.Errorf("panicJanusR7: ok=%v err=%v", ok, err)
	}
}

func TestList(t *testing.T) {
	code, out, stderr := runJanus(t, "list", exampleBin)
	if code != 0 {
		t.Fatalf("list failed: %s", stderr)
	}
	for _, f := range exampleFuncs {
		if !regexp.MustCompile(`(?m)^0x[0-9a-f]{16} +\d+  example\.com/basic\.` + f + `$`).MatchString(out) {
			t.Errorf("list output lacks example.com/basic.%s", f)
		}
	}
	if !strings.Contains(out, "go1.26") || !strings.Contains(out, "example.com/basic") {
		t.Errorf("list header lacks build info: %s", strings.SplitN(out, "\n", 2)[0])
	}
}

func TestRejectsNonArm64(t *testing.T) {
	self, err := os.Executable() // the test binary, built for the host
	if err != nil {
		t.Fatal(err)
	}
	code, _, stderr := runJanus(t, "list", self)
	if code != 1 || !strings.Contains(stderr, "Stage: binary validation") {
		if code == 0 {
			t.Skip("host is linux/arm64")
		}
		t.Fatalf("expected binary validation failure, got %d: %s", code, stderr)
	}
}

func TestExtractShape(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.Add")
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	add, _ := b.lookup("example.com/basic.Add")
	want := fmt.Sprintf(`{ name := "example.com/basic.Add", base := 0x%x, words := [0x8b010000, 0xd65f03c0] } ]`, add.Addr)
	for _, s := range []string{"import Janus\n", "namespace Extracted\nopen Janus\n", "def segments : List Segment := [\n  " + want,
		"def stubs : List Stub := []\n", "def exitAddr : Nat := 0\n",
		"def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }\n",
		fmt.Sprintf("def entry : Nat := 0x%x\n", add.Addr), "end Extracted\n"} {
		if !strings.Contains(string(lean), s) {
			t.Errorf("Extracted.lean lacks %q:\n%s", s, lean)
		}
	}
	id := readIdentity(t, dir)
	if id.Symbol != "example.com/basic.Add" || id.GOARCH != "arm64" || id.GOOS != "linux" || id.GoVersion == "" ||
		id.MainModule != "example.com/basic" || id.ExtractedSha256 != sha256Hex(lean) || id.Size != add.Size {
		t.Errorf("unexpected identity: %+v", id)
	}
	if len(id.BinarySha256) != 64 {
		t.Errorf("binary hash %q", id.BinarySha256)
	}
}

func TestExtractCalleesAndStubs(t *testing.T) {
	stubNames := func(id *Identity) map[string]string {
		m := map[string]string{}
		for _, s := range id.Stubs {
			m[s.Name] = s.Kind
		}
		return m
	}
	get := readIdentity(t, mustExtract(t, "example.com/basic.Get"))
	if len(get.Functions) != 1 || stubNames(get)["runtime.panicBounds"] != "panic" ||
		stubNames(get)["runtime.morestack_noctxt.abi0"] != "morestack" {
		t.Errorf("Get: %+v %+v", get.Functions, get.Stubs)
	}
	div := readIdentity(t, mustExtract(t, "example.com/basic.Div"))
	if stubNames(div)["runtime.panicdivide"] != "panic" {
		t.Errorf("Div stubs: %+v", div.Stubs)
	}
	three := readIdentity(t, mustExtract(t, "example.com/basic.AddThree"))
	if len(three.Functions) != 2 || three.Functions[0].Name != "example.com/basic.AddThree" ||
		three.Functions[1].Name != "example.com/basic.Add" {
		t.Errorf("AddThree functions: %+v", three.Functions)
	}
	// Leaf functions have no stack check and so no stubs.
	sum := readIdentity(t, mustExtract(t, "example.com/basic.Sum"))
	if len(sum.Functions) != 1 || len(sum.Stubs) != 0 {
		t.Errorf("Sum: %+v %+v", sum.Functions, sum.Stubs)
	}
}

func TestMaxFunctions(t *testing.T) {
	dir := filepath.Join(t.TempDir(), "main")
	code, _, stderr := runJanus(t, "extract", exampleBin, "main.main", dir, "--max-functions", "4")
	if code != 1 || !strings.Contains(stderr, "reaches more than 4 functions") || !strings.Contains(stderr, "--max-functions") {
		t.Fatalf("expected max-functions failure, got %d: %s", code, stderr)
	}
	if _, err := os.Stat(filepath.Join(dir, "identity.json")); err == nil {
		t.Error("failed extraction wrote identity.json")
	}
}

func TestUnknownSymbol(t *testing.T) {
	code, _, stderr := runJanus(t, "extract", exampleBin, "example.com/basic.Nope", t.TempDir())
	if code != 1 || !strings.Contains(stderr, "Stage: function selection") {
		t.Fatalf("got %d: %s", code, stderr)
	}
}

// objdumpWords disassembles [start, stop) and returns address -> word and, for direct
// branches, address -> target.
func objdumpWords(t *testing.T, start, stop uint64) (map[uint64]uint32, map[uint64]uint64) {
	t.Helper()
	tool, err := exec.LookPath("aarch64-linux-gnu-objdump")
	if err != nil {
		t.Skip("aarch64-linux-gnu-objdump not installed")
	}
	out, err := exec.Command(tool, "-d", "-z", fmt.Sprintf("--start-address=0x%x", start),
		fmt.Sprintf("--stop-address=0x%x", stop), exampleBin).Output()
	if err != nil {
		t.Fatal(err)
	}
	re := regexp.MustCompile(`^\s*([0-9a-f]+):\s+([0-9a-f]{8})\s`)
	br := regexp.MustCompile(`\t(b|bl|b\.[a-z]+|cbz|cbnz|tbz|tbnz)\t(?:.*, )?([0-9a-f]+) <`)
	m := map[uint64]uint32{}
	targets := map[uint64]uint64{}
	sc := bufio.NewScanner(bytes.NewReader(out))
	for sc.Scan() {
		if g := re.FindStringSubmatch(sc.Text()); g != nil {
			a, _ := strconv.ParseUint(g[1], 16, 64)
			w, _ := strconv.ParseUint(g[2], 16, 32)
			m[a] = uint32(w)
			if b := br.FindStringSubmatch(sc.Text()); b != nil {
				targets[a], _ = strconv.ParseUint(b[2], 16, 64)
			}
		}
	}
	return m, targets
}

func TestObjdumpCrossCheck(t *testing.T) {
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	branches := 0
	defer func() {
		if branches < 100 {
			t.Errorf("only %d branches cross-checked", branches)
		}
	}()
	for _, f := range append(exampleFuncs, "main.main") {
		sym := "example.com/basic." + f
		if f == "main.main" {
			sym = f
		}
		x, err := extractFrom(b, sym, 1000)
		if err != nil {
			t.Fatalf("%s: %v", sym, err)
		}
		checked := 0
		for _, s := range x.Segments {
			if checked > 200 { // main.main reaches hundreds of runtime functions; sample them
				break
			}
			checked++
			dump, targets := objdumpWords(t, s.Base, s.Base+s.Size)
			for i, w := range s.Words {
				a := s.Base + 4*uint64(i)
				if got, ok := dump[a]; !ok || got != w {
					t.Errorf("%s: word at %#x is %#08x, objdump says %#08x (present %v)", s.Name, a, w, got, ok)
				}
				// The reachability decoder agrees with objdump on every direct branch.
				tgt, isBr := branchTarget(w, a)
				if isBr {
					branches++
				}
				want, objBr := targets[a]
				if isBr != objBr || tgt != want {
					t.Errorf("%s: branch at %#x (%#08x): decoder %#x %v, objdump %#x %v", s.Name, a, w, tgt, isBr, want, objBr)
				}
			}
			// Everything trimmed after the last word must be zero padding.
			for a := s.Base + 4*uint64(len(s.Words)); a < s.Base+s.Size; a += 4 {
				if dump[a] != 0 {
					t.Errorf("%s: trimmed non-zero word %#08x at %#x", s.Name, dump[a], a)
				}
			}
			if len(s.Words) == 0 || s.Words[len(s.Words)-1] == 0 {
				t.Errorf("%s: bad trimming", s.Name)
			}
		}
	}
}

func TestCheckAndTamper(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.Get")
	if code, out, stderr := runJanus(t, "check", dir); code != 0 || !strings.HasPrefix(out, "Valid:") {
		t.Fatalf("check of fresh artifacts failed: %d %s", code, stderr)
	}
	leanPath := filepath.Join(dir, "Extracted.lean")
	orig, _ := os.ReadFile(leanPath)

	t.Run("edited Extracted.lean", func(t *testing.T) {
		defer os.WriteFile(leanPath, orig, 0o644)
		os.WriteFile(leanPath, bytes.Replace(orig, []byte("0xf8637800"), []byte("0xf8637801"), 1), 0o644)
		code, out, stderr := runJanus(t, "check", dir)
		if code != 1 || out != "" || !strings.HasPrefix(stderr, "Invalid: ") ||
			!strings.Contains(stderr, "was modified after extraction") || !strings.Contains(stderr, "Stage: extraction integrity") ||
			!strings.Contains(stderr, "Next: Rerun janus extract") {
			t.Fatalf("got %d %q %q", code, out, stderr)
		}
	})

	t.Run("forged Extracted.lean and identity hash", func(t *testing.T) {
		idPath := filepath.Join(dir, "identity.json")
		origID, _ := os.ReadFile(idPath)
		defer os.WriteFile(leanPath, orig, 0o644)
		defer os.WriteFile(idPath, origID, 0o644)
		forged := bytes.Replace(orig, []byte("0xf8637800"), []byte("0xf8637801"), 1)
		os.WriteFile(leanPath, forged, 0o644)
		os.WriteFile(idPath, bytes.Replace(origID, []byte(sha256Hex(orig)), []byte(sha256Hex(forged)), 1), 0o644)
		code, _, stderr := runJanus(t, "check", dir)
		if code != 1 || !strings.Contains(stderr, "differs from the regenerated extraction") ||
			!strings.Contains(stderr, "Stage: extraction integrity") {
			t.Fatalf("got %d %q", code, stderr)
		}
	})

	t.Run("changed binary", func(t *testing.T) {
		// Copy the binary next to the artifacts, extract from the copy, then change one byte.
		d := t.TempDir()
		bin := filepath.Join(d, "bin")
		data, _ := os.ReadFile(exampleBin)
		os.WriteFile(bin, data, 0o755)
		art := filepath.Join(d, "art")
		if code, _, stderr := runJanus(t, "extract", bin, "example.com/basic.Get", art); code != 0 {
			t.Fatal(stderr)
		}
		mod := append([]byte(nil), data...)
		mod[len(mod)/2] ^= 0xff
		os.WriteFile(bin, mod, 0o755)
		code, _, stderr := runJanus(t, "check", art)
		if code != 1 || !strings.Contains(stderr, "Invalid: Binary changed since extraction") ||
			!strings.Contains(stderr, "Stage: binary identity") {
			t.Fatalf("got %d %q", code, stderr)
		}
		// --binary pointing at the original content is accepted.
		if code, _, stderr := runJanus(t, "check", art, "--binary", exampleBin); code != 0 {
			t.Fatalf("check --binary original: %s", stderr)
		}
		os.Remove(bin)
		code, _, stderr = runJanus(t, "check", art)
		if code != 1 || !strings.Contains(stderr, "Cannot read binary") || !strings.Contains(stderr, "--binary") {
			t.Fatalf("missing binary: got %d %q", code, stderr)
		}
	})

	t.Run("missing manifest", func(t *testing.T) {
		code, _, stderr := runJanus(t, "check", t.TempDir())
		if code != 1 || !strings.Contains(stderr, "Stage: artifact layout") {
			t.Fatalf("got %d %q", code, stderr)
		}
	})

	t.Run("verify removes stale report on failure", func(t *testing.T) {
		defer os.WriteFile(leanPath, orig, 0o644)
		report := filepath.Join(dir, "verified.json")
		os.WriteFile(report, []byte("{}"), 0o644)
		os.WriteFile(leanPath, append(append([]byte(nil), orig...), '\n'), 0o644)
		code, out, stderr := runJanus(t, "verify", dir, "--proof", filepath.Join(dir, "nope.lean"))
		if code != 1 || out != "" || !strings.Contains(stderr, "Invalid:") {
			t.Fatalf("got %d %q", code, stderr)
		}
		if _, err := os.Stat(report); err == nil {
			t.Fatal("stale verified.json survived a failed verify")
		}
	})
}

// TestVerify runs Lean (also with -short). It needs lake on PATH (or ~/.elan/bin); the Janus
// library of the checkout is built on first use.
func TestVerify(t *testing.T) {
	t.Parallel()
	needLean(t)
	dir := mustExtract(t, "example.com/basic.Get")
	proofs := t.TempDir()
	write := func(name, body string) string {
		p := filepath.Join(proofs, name)
		if err := os.WriteFile(p, []byte(body), 0o644); err != nil {
			t.Fatal(err)
		}
		return p
	}
	verify := func(proof string, extra ...string) (int, string, string) {
		return runJanus(t, append([]string{"verify", dir, "--proof", proof, "--janus-root", repoRoot}, extra...)...)
	}
	report := filepath.Join(dir, "verified.json")

	good := write("Good.lean", "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = Extracted.entry := rfl\n"+
		"theorem segs : Extracted.program.segments.length = 1 := by decide\nend Proof\n")
	code, out, stderr := verify(good)
	if code != 0 || !strings.HasPrefix(out, "Verified: Proof.correctness\n") {
		t.Fatalf("good proof: %d\n%s\n%s", code, out, stderr)
	}
	var r verifiedReport
	b, err := os.ReadFile(report)
	if err != nil || json.Unmarshal(b, &r) != nil {
		t.Fatalf("verified.json: %v", err)
	}
	if r.Theorem != "Proof.correctness" || r.Statement != "Proof.correctness : Extracted.entry = Extracted.entry" ||
		len(r.Axioms) != 0 || r.LeanVersion == "" || r.KernelReplay.Status == "" || r.Symbol != "example.com/basic.Get" {
		t.Errorf("unexpected report: %+v", r)
	}
	if code, out, stderr := verify(good, "--theorem", "Proof.segs"); code != 0 || !strings.Contains(out, "Verified: Proof.segs") {
		t.Fatalf("decide proof: %d %s %s", code, out, stderr)
	}
	// The checked-in fixtures (cmd/janus/testdata, also used in docs/CLI.md).
	if code, out, stderr := verify(filepath.Join("testdata", "Trivial.lean")); code != 0 || !strings.HasPrefix(out, "Verified: Proof.correctness\n") {
		t.Fatalf("testdata/Trivial.lean: %d %s %s", code, out, stderr)
	}
	if code, _, stderr := verify(filepath.Join("testdata", "Sorry.lean")); code != 1 || !strings.Contains(stderr, "disallowed axioms: sorryAx") {
		t.Fatalf("testdata/Sorry.lean: %d %s", code, stderr)
	}

	rejected := []struct {
		name, body, extra, want, stage string
	}{
		{"Sorry.lean", "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = 0 := sorry\nend Proof\n",
			"", "disallowed axioms: sorryAx", "axiom audit"},
		{"Native.lean", "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry > 0 := by native_decide\nend Proof\n",
			"", "disallowed axioms", "axiom audit"},
		{"Axiom.lean", "import Extracted\nnamespace Proof\naxiom cheat : Extracted.entry = 0\ntheorem correctness : Extracted.entry = 0 := cheat\nend Proof\n",
			"", "disallowed axioms: Proof.cheat", "axiom audit"},
		{"Broken.lean", "import Extracted\nnamespace Proof\ntheorem correctness : Extracted.entry = 0 := rfl\nend Proof\n",
			"", "Lean errors (", "proof checking"},
		{"Missing.lean", "import Extracted\nnamespace Proof\ntheorem other : True := trivial\nend Proof\n",
			"", "does not define Proof.correctness", "theorem audit"},
		{"Def.lean", "import Extracted\nnamespace Proof\ndef correctness : Nat := Extracted.entry\nend Proof\n",
			"", "is a definition, not a theorem", "theorem audit"},
		{"Foreign.lean", "import Extracted\nnamespace Proof\ntheorem x : True := trivial\nend Proof\n",
			"Nat.add_comm", "not in the proof module", "theorem audit"},
		{"Evil.lean", "import Extracted\nimport Lean\nset_option debug.skipKernelTC true in\n" +
			"run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {\n" +
			"  name := `Proof.correctness, levelParams := [],\n" +
			"  type := Lean.mkApp3 (Lean.mkConst ``Eq [1]) (Lean.mkConst ``Nat) (Lean.mkConst `Extracted.entry) (Lean.mkNatLit 0),\n" +
			"  value := Lean.mkConst ``True.intro })\n",
			"", "Kernel replay rejected", "kernel replay"},
	}
	// Each rejection runs in parallel on its own extraction of Get (so each has its own
	// verified.json to withdraw).
	t.Run("rejected", func(t *testing.T) {
		for _, c := range rejected {
			t.Run(c.name, func(t *testing.T) {
				t.Parallel()
				dir := mustExtract(t, "example.com/basic.Get")
				report := filepath.Join(dir, "verified.json")
				os.WriteFile(report, []byte("{}"), 0o644)
				extra := []string{}
				if c.extra != "" {
					extra = []string{"--theorem", c.extra}
				}
				code, out, stderr := runJanus(t, append([]string{"verify", dir, "--proof", write(c.name, c.body), "--janus-root", repoRoot}, extra...)...)
				if code != 1 || out != "" || !strings.HasPrefix(stderr, "Invalid: ") || !strings.Contains(stderr, c.want) ||
					!strings.Contains(stderr, "Stage: "+c.stage) {
					t.Fatalf("got %d\nstdout: %s\nstderr: %s", code, out, stderr)
				}
				if _, err := os.Stat(report); err == nil {
					t.Fatal("verified.json not removed")
				}
			})
		}
	})
	if code, _, stderr := verify(good, "--theorem", "Proof.correctness\n#eval 1"); code != 1 || !strings.Contains(stderr, "not a plain dotted Lean name") {
		t.Fatalf("theorem injection: %d %s", code, stderr)
	}
}
