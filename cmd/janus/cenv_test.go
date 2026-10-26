package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"
)

// buildCEnvAmd64 builds examples/cgo/cmd/cenv (the C environment examples, docs/FFI.md
// sections 2-4) for linux/amd64 with the host gcc (skips without one); ldflags are extra
// CGO_LDFLAGS (the --no-relax build).
func buildCEnvAmd64(t *testing.T, ldflags string) string {
	t.Helper()
	if _, err := exec.LookPath("gcc"); err != nil {
		t.Skip("no gcc for the cgo example")
	}
	bin := filepath.Join(t.TempDir(), "examples-cenv-amd64")
	cmd := exec.Command("go", "build", "-buildmode=exe", "-trimpath", "-buildvcs=false", "-o", bin, "./cmd/cenv")
	cmd.Dir = filepath.Join(repoRoot, "examples", "cgo")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64", "GOAMD64=v1", "CGO_ENABLED=1", "CC=gcc")
	if ldflags != "" {
		cmd.Env = append(cmd.Env, "CGO_LDFLAGS=-g -O2 "+ldflags)
	}
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("building the C environment example: %v\n%s", err, out)
	}
	return bin
}

func cenvExtract(t *testing.T, b *Binary, sym string) *Extraction {
	t.Helper()
	x, err := extractWith(b, sym, defaultMaxFunctions, []string{"runtime.convT64", "runtime.convT32", "runtime.convTnoptr"})
	if err != nil {
		t.Fatalf("%s: %v", sym, err)
	}
	return x
}

func cenvSegNames(x *Extraction) []string {
	var n []string
	for _, s := range x.Segments {
		n = append(n, s.Name)
	}
	return n
}

// The C environment of an extraction (cenv.go): PLT entries as named external stubs, writable C
// data and the TLS image as Lean definitions, code addresses C code materialises (an immediate
// operand, the //export wrapper's _cgoexp_ function) followed, and the cgocallback stub.
func TestCEnvExtraction(t *testing.T) {
	b, err := loadBinary(buildCEnvAmd64(t, ""))
	if err != nil {
		t.Fatal(err)
	}

	// libc through the PLT: every call is a stub sym@plt, nothing of libc is copied
	x := cenvExtract(t, b, "e_libc")
	ext := map[string]bool{}
	for _, s := range x.Stubs {
		if s.Kind == stubExternal {
			ext[s.Name] = true
		}
	}
	for _, n := range []string{"strlen@plt", "malloc@plt", "__memcpy_chk@plt", "memcpy@plt", "free@plt"} {
		if !ext[n] {
			t.Errorf("e_libc: %s is not an external stub: %+v", n, x.Stubs)
		}
	}
	if got := cenvSegNames(x); !slices.Equal(got, []string{"e_libc"}) {
		t.Errorf("e_libc: segments %q, want only e_libc", got)
	}

	// TLS: the image with Go's runtime.tlsg and the C __thread variables
	x = cenvExtract(t, b, "e_tls_add")
	if x.TLS == nil {
		t.Fatal("e_tls_add: no TLS image")
	}
	var vars []string
	for _, v := range x.TLS.Vars {
		vars = append(vars, v.Name)
	}
	for _, n := range []string{"runtime.tlsg", "e_tls", "e_tls_ie"} {
		if !slices.Contains(vars, n) {
			t.Errorf("TLS image vars %q lack %q", vars, n)
		}
	}
	if !strings.Contains(string(x.Lean), "def tls : TLSImage") {
		t.Error("Extracted.lean has no TLS image")
	}

	// writable C data
	x = cenvExtract(t, b, "e_bump")
	var data []string
	for _, d := range x.CData {
		data = append(data, d.Name)
	}
	for _, n := range []string{"e_counter", "e_scale"} {
		if !slices.Contains(data, n) {
			t.Errorf("e_bump: cdata %q lacks %q", data, n)
		}
	}
	if !strings.Contains(string(x.Lean), "def cdata : List CData") {
		t.Error("Extracted.lean has no cdata")
	}

	// a GOT slot with a dynamic relocation (R_*_GLOB_DAT of libc's environ): not copied, named
	x = cenvExtract(t, b, "e_env_at")
	if !slices.ContainsFunc(x.DynGOT, func(d DynGOT) bool { return d.Name == "environ" && d.Slot%8 == 0 }) {
		t.Errorf("e_env_at: dyngot %+v lacks environ", x.DynGOT)
	}
	for _, d := range x.Data {
		for _, g := range x.DynGOT {
			if d.Base <= g.Slot && g.Slot < d.Base+uint64(len(d.Bytes)) {
				t.Errorf("e_env_at: the dynamic GOT slot 0x%x is copied as data (%s)", g.Slot, d.Name)
			}
		}
	}
	if !strings.Contains(string(x.Lean), "def dyngot : List DynGOT") {
		t.Error("Extracted.lean has no dyngot")
	}

	// a function pointer passed as an immediate (mov $e_cmp_i64, %rdx)
	x = cenvExtract(t, b, "e_argmin_i64")
	if !slices.Contains(cenvSegNames(x), "e_cmp_i64") {
		t.Errorf("e_argmin_i64: segments %q lack the comparator e_cmp_i64", cenvSegNames(x))
	}
	if !slices.ContainsFunc(x.Dynamic, func(d DynTarget) bool { return d.Name == "e_cmp_i64" && d.Via == "c-immediate" }) {
		t.Errorf("e_argmin_i64: e_cmp_i64 not a c-immediate target: %+v", x.Dynamic)
	}

	// //export: the Go function behind crosscall2, and cgocallback as an external stub
	x = cenvExtract(t, b, "e_callgo")
	got := cenvSegNames(x)
	for _, n := range []string{"GoTwice", "crosscall2"} {
		if !slices.Contains(got, n) {
			t.Errorf("e_callgo: segments %q lack %q", got, n)
		}
	}
	if !slices.ContainsFunc(got, func(n string) bool { return strings.Contains(n, "_cgoexp_") && strings.HasSuffix(n, "_GoTwice") }) {
		t.Errorf("e_callgo: segments %q lack the exported Go function", got)
	}
	if !slices.ContainsFunc(x.Stubs, func(s Stub) bool { return s.Name == "runtime.cgocallback.abi0" && s.Kind == stubExternal }) {
		t.Errorf("e_callgo: runtime.cgocallback.abi0 is not an external stub: %+v", x.Stubs)
	}
}

// A static GOT slot (RELRO, no dynamic relocation) is copied as read-only data when the code
// keeps its GOT load (the --no-relax build).
func TestCEnvStaticGOT(t *testing.T) {
	b, err := loadBinary(buildCEnvAmd64(t, "-Wl,--no-relax"))
	if err != nil {
		t.Fatal(err)
	}
	x := cenvExtract(t, b, "e_bump")
	var data []string
	for _, d := range x.Data {
		data = append(data, d.Name)
	}
	for _, n := range []string{"got:e_counter", "got:e_scale"} {
		if !slices.Contains(data, n) {
			t.Errorf("e_bump (--no-relax): data %q lacks %q", data, n)
		}
	}
}

// The cgocall contract states Go's TLS g slot at FS-8; in a binary whose C code has __thread
// variables it is elsewhere, so extracting a Go function that reaches runtime.cgocall is refused.
func TestCEnvCgoTLSRefused(t *testing.T) {
	b, err := loadBinary(buildCEnvAmd64(t, ""))
	if err != nil {
		t.Fatal(err)
	}
	_, err = extractWith(b, "example.com/cgo/cenv._Cfunc_e_bump.abi0", defaultMaxFunctions, []string{"runtime.convT64", "runtime.convT32", "runtime.convTnoptr"})
	if err == nil || !strings.Contains(err.Error(), "TLS g slot") {
		t.Fatalf("extracting a cgocall in a binary with C __thread variables: err = %v, want the TLS g slot refusal", err)
	}
}
