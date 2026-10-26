package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"runtime"
	"strings"
	"testing"
)

const buildModeProg = `package main

import "unsafe"

//go:noinline
func Add(a, b int) int { return a + b }

//go:noinline
func Word(p *byte) uint64 { return *(*uint64)(unsafe.Pointer(p)) }

var fn = Add

func main() {
	var b [16]byte
	println(Add(1, 2), Word(&b[0]), fn(3, 4))
}
`

// buildModeBinary builds buildModeProg (plus extra files) with the given go build flags and
// environment. With skip, a failed build skips the test (sanitizer toolchains are optional).
func buildModeBinary(t *testing.T, env []string, skip bool, extra map[string]string, flags ...string) string {
	t.Helper()
	if testing.Short() {
		t.Skip("builds a Go program")
	}
	dir := t.TempDir()
	files := map[string]string{"go.mod": "module example.com/bm\n\ngo 1.26\n", "main.go": buildModeProg}
	for k, v := range extra {
		files[k] = v
	}
	for name, src := range files {
		if err := os.WriteFile(filepath.Join(dir, name), []byte(src), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	bin := filepath.Join(dir, "prog")
	cmd := exec.Command("go", append(append([]string{"build", "-trimpath", "-buildvcs=false"}, flags...), "-o", bin, ".")...)
	cmd.Dir = dir
	cmd.Env = append(append(os.Environ(), "GOTOOLCHAIN=go1.26.0", "GOOS=linux", "GOFLAGS="), env...)
	if out, err := cmd.CombinedOutput(); err != nil {
		if skip {
			t.Skipf("cannot build with %v %v: %v\n%s", env, flags, err, out)
		}
		t.Fatalf("go build %v: %v\n%s", flags, err, out)
	}
	return bin
}

// extractModes runs janus extract and janus check, and returns the recorded build modes and
// the extract stderr.
func extractModes(t *testing.T, bin, sym string, extra ...string) ([]string, string) {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "art")
	code, _, stderr := runJanus(t, append([]string{"extract", bin, sym, dir}, extra...)...)
	if code != 0 {
		t.Fatalf("extract %s failed: %s", sym, stderr)
	}
	raw, err := os.ReadFile(filepath.Join(dir, "identity.json"))
	if err != nil {
		t.Fatal(err)
	}
	id := readIdentity(t, dir)
	if (len(id.BuildModes) == 0) == strings.Contains(string(raw), `"buildModes"`) {
		t.Errorf("buildModes field present iff modes were detected; got %v in\n%s", id.BuildModes, raw)
	}
	if code, out, errb := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check after extract failed:\n%s%s", out, errb)
	}
	return id.BuildModes, stderr
}

func hostAmd64Cgo(t *testing.T, cc string) {
	t.Helper()
	if runtime.GOARCH != "amd64" || runtime.GOOS != "linux" {
		t.Skip("sanitizer builds need a linux/amd64 host")
	}
	if _, err := exec.LookPath(cc); err != nil {
		t.Skipf("no %s", cc)
	}
}

func TestBuildModeDefault(t *testing.T) {
	for _, arch := range []string{"arm64", "amd64"} {
		bin := buildModeBinary(t, []string{"GOARCH=" + arch, "CGO_ENABLED=0"}, false, nil)
		for _, sym := range []string{"main.Add", "main.Word"} {
			modes, stderr := extractModes(t, bin, sym)
			if modes != nil || strings.Contains(stderr, "note: built with") {
				t.Errorf("%s %s: modes %v, stderr %q; want none", arch, sym, modes, stderr)
			}
		}
	}
}

func TestBuildModeCover(t *testing.T) {
	for _, arch := range []string{"arm64", "amd64"} {
		bin := buildModeBinary(t, []string{"GOARCH=" + arch, "CGO_ENABLED=0"}, false, nil, "-cover", "-covermode=count")
		modes, stderr := extractModes(t, bin, "main.Add")
		if !reflect.DeepEqual(modes, []string{"cover"}) {
			t.Errorf("%s: modes %v, want [cover]", arch, modes)
		}
		if !strings.Contains(stderr, noteCover+"\n") {
			t.Errorf("%s: no cover note in stderr:\n%s", arch, stderr)
		}
	}
}

func TestBuildModeCheckptr(t *testing.T) {
	for _, arch := range []string{"arm64", "amd64"} {
		bin := buildModeBinary(t, []string{"GOARCH=" + arch, "CGO_ENABLED=0"}, false, nil, "-gcflags=-d=checkptr")
		// Word converts unsafe.Pointer to *uint64: checkptrAlignment.
		modes, stderr := extractModes(t, bin, "main.Word")
		if !reflect.DeepEqual(modes, []string{"checkptr"}) || !strings.Contains(stderr, noteCheckptr) {
			t.Errorf("%s Word: modes %v, stderr %q; want [checkptr] and its note", arch, modes, stderr)
		}
		if modes, _ := extractModes(t, bin, "main.Word", "--contract", "runtime.checkptr*"); !reflect.DeepEqual(modes, []string{"checkptr"}) {
			t.Errorf("%s Word --contract: modes %v, want [checkptr]", arch, modes)
		}
		// Add does no pointer conversion: no checkptr call in its code.
		if modes, _ := extractModes(t, bin, "main.Add"); modes != nil {
			t.Errorf("%s Add: modes %v, want none", arch, modes)
		}
	}
}

func TestBuildModeSpectreRet(t *testing.T) {
	bin := buildModeBinary(t, []string{"GOARCH=amd64", "GOAMD64=v1", "CGO_ENABLED=0"}, false, nil,
		"-gcflags=-spectre=ret", "-asmflags=-spectre=ret")
	modes, stderr := extractModes(t, bin, "main.Add")
	if !reflect.DeepEqual(modes, []string{"spectre=ret"}) || !strings.Contains(stderr, noteSpectre) {
		t.Errorf("modes %v, stderr %q; want [spectre=ret] and its note", modes, stderr)
	}
}

// rejectBuild checks that extraction of an entry that calls no instrumentation still fails with
// the build mode's error, and that the error is a code-extraction diag.
func rejectBuild(t *testing.T, bin string, want ...string) {
	t.Helper()
	code, _, stderr := runJanus(t, "extract", bin, "main.Add", filepath.Join(t.TempDir(), "art"))
	if code == 0 {
		t.Fatalf("extract succeeded; want a build-mode error")
	}
	for _, w := range append(want, "Stage: code extraction") {
		if !strings.Contains(stderr, w) {
			t.Errorf("stderr lacks %q:\n%s", w, stderr)
		}
	}
}

func TestBuildModeRace(t *testing.T) {
	hostAmd64Cgo(t, "gcc")
	bin := buildModeBinary(t, []string{"GOARCH=amd64", "CGO_ENABLED=1", "CC=gcc"}, true, nil, "-race")
	rejectBuild(t, bin, "built with -race", "concurrency is out of scope")
}

func TestBuildModeMsan(t *testing.T) {
	hostAmd64Cgo(t, "clang")
	bin := buildModeBinary(t, []string{"GOARCH=amd64", "CGO_ENABLED=1", "CC=clang"}, true, nil, "-msan")
	rejectBuild(t, bin, "built with -msan", "MemorySanitizer")
}

func TestBuildModeAsan(t *testing.T) {
	hostAmd64Cgo(t, "gcc")
	bin := buildModeBinary(t, []string{"GOARCH=amd64", "CGO_ENABLED=1", "CC=gcc"}, true, nil, "-asan")
	rejectBuild(t, bin, "built with -asan", "AddressSanitizer")
}

// A libFuzzer build is normally a c-archive; linked with libFuzzer's runtime without its main
// (libclang_rt.fuzzer_no_main) it is an executable Janus can load, and must reject.
func TestBuildModeLibfuzzer(t *testing.T) {
	hostAmd64Cgo(t, "clang")
	out, err := exec.Command("clang", "--print-runtime-dir").Output()
	if err != nil {
		t.Skipf("clang --print-runtime-dir: %v", err)
	}
	lib := filepath.Join(strings.TrimSpace(string(out)), "libclang_rt.fuzzer_no_main.a")
	if _, err := os.Stat(lib); err != nil {
		lib = filepath.Join(filepath.Dir(strings.TrimSpace(string(out))), "linux", "libclang_rt.fuzzer_no_main-x86_64.a")
	}
	if _, err := os.Stat(lib); err != nil {
		t.Skip("no libclang_rt.fuzzer_no_main")
	}
	fuzz := `package main

import "C"

//export LLVMFuzzerTestOneInput
func LLVMFuzzerTestOneInput(p *C.char, n C.size_t) C.int {
	if n > 3 && *p == 'a' {
		return 1
	}
	return 0
}
`
	bin := buildModeBinary(t, []string{"GOARCH=amd64", "CGO_ENABLED=1", "CC=clang", "CGO_LDFLAGS=" + lib + " -lstdc++ -lm"},
		true, map[string]string{"fuzz.go": fuzz}, "-tags=libfuzzer", "-gcflags=all=-d=libfuzzer")
	rejectBuild(t, bin, "built with -d=libfuzzer", "__sancov_cntrs")
}

// The decision table on synthetic signals: every detection rule on its own.
func TestBuildModeClassify(t *testing.T) {
	sig := func(names []string, addrs map[string]uint64, sections []string, settings map[string]string) buildSignals {
		var s buildSignals
		for _, n := range names {
			s.add(n, 0, false)
		}
		for n, a := range addrs {
			s.add(n, a, true)
		}
		s.sections = map[string]bool{}
		for _, n := range sections {
			s.sections[n] = true
		}
		s.settings = settings
		return s
	}
	rejects := []struct {
		s    buildSignals
		want string
	}{
		{sig([]string{"runtime.racefuncenter"}, nil, nil, nil), "built with -race"},
		{sig([]string{"runtime.raceread"}, nil, nil, nil), "built with -race"},
		{sig([]string{"__tsan_init"}, nil, nil, nil), "built with -race"},
		{sig(nil, nil, nil, map[string]string{"-race": "true"}), "built with -race"},
		{sig([]string{"runtime.msanread"}, nil, nil, nil), "built with -msan"},
		{sig([]string{"__msan_init"}, nil, nil, nil), "built with -msan"},
		{sig(nil, nil, nil, map[string]string{"-msan": "true"}), "built with -msan"},
		{sig([]string{"runtime.asanread"}, nil, nil, nil), "built with -asan"},
		{sig([]string{"__asan_init"}, nil, nil, nil), "built with -asan"},
		{sig(nil, nil, nil, map[string]string{"-asan": "true"}), "built with -asan"},
		{sig([]string{"runtime.libfuzzerTraceCmp1"}, nil, nil, nil), "built with -d=libfuzzer"},
		{sig([]string{"runtime.libfuzzerTraceConstCmp8"}, nil, nil, nil), "built with -d=libfuzzer"},
		{sig([]string{"runtime.libfuzzerHookStrCmp"}, nil, nil, nil), "built with -d=libfuzzer"},
		{sig(nil, nil, []string{"__sancov_cntrs"}, nil), "built with -d=libfuzzer"},
	}
	for _, c := range rejects {
		modes, err := classifyBuildModes(c.s)
		d, ok := err.(*diag)
		if !ok || !strings.HasPrefix(d.Msg, c.want) || d.Stage != "code extraction" || modes != nil {
			t.Errorf("%v: got %v, %v; want %q", c.s.names, modes, err, c.want)
		}
	}
	accepts := []struct {
		s    buildSignals
		want []string
	}{
		{sig(nil, map[string]uint64{"runtime.covctrs": 0x100, "runtime.ecovctrs": 0x100}, nil, nil), nil},
		{sig(nil, map[string]uint64{"runtime.covctrs": 0x100, "runtime.ecovctrs": 0x130}, nil, nil), []string{"cover"}},
		{sig([]string{"runtime.addCovMeta"}, nil, nil, nil), []string{"cover"}},
		{sig(nil, nil, nil, map[string]string{"-cover": "true"}), []string{"cover"}},
		{sig([]string{"runtime.retpolineR15.abi0"}, nil, nil, nil), []string{"spectre=ret"}},
		{sig([]string{"runtime.retpolineAX", "runtime.addCovMeta"}, nil, nil, nil), []string{"cover", "spectre=ret"}},
		{sig([]string{"runtime.checkptrAlignment"}, nil, nil, nil), nil}, // checkptr depends on the extracted code
	}
	for _, c := range accepts {
		modes, err := classifyBuildModes(c.s)
		if err != nil || !reflect.DeepEqual(modes, c.want) {
			t.Errorf("%v %v: got %v, %v; want %v", c.s.names, c.s.addrs, modes, err, c.want)
		}
	}
	x := &Extraction{Segments: []Segment{{Name: "main.F"}, {Name: "runtime.checkptrArithmetic"}}}
	if got := withCheckptr([]string{"cover", "spectre=ret"}, x); !reflect.DeepEqual(got, []string{"cover", "checkptr", "spectre=ret"}) {
		t.Errorf("withCheckptr = %v", got)
	}
	if got := withCheckptr(nil, &Extraction{Segments: []Segment{{Name: "main.F"}}}); got != nil {
		t.Errorf("withCheckptr without a checkptr call = %v, want nil", got)
	}
}
