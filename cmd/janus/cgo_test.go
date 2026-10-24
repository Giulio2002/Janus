package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// buildCgoAmd64 builds examples/cgo for linux/amd64 with the host gcc (skips without one).
func buildCgoAmd64(t *testing.T) string {
	t.Helper()
	if _, err := exec.LookPath("gcc"); err != nil {
		t.Skip("no gcc for the cgo example")
	}
	bin := filepath.Join(t.TempDir(), "examples-cgo-amd64")
	cmd := exec.Command("go", "build", "-buildmode=exe", "-trimpath", "-o", bin, "./cmd")
	cmd.Dir = filepath.Join(repoRoot, "examples", "cgo")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64", "GOAMD64=v1", "CGO_ENABLED=1", "CC=gcc")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("building the cgo example: %v\n%s", err, out)
	}
	return bin
}

// A cgo Go function's extraction follows the function-pointer variable to the C wrapper and
// from there to the C function; the cgo boundary functions are external stubs.
func TestCgoExtraction(t *testing.T) {
	bin := buildCgoAmd64(t)
	b, err := loadBinary(bin)
	if err != nil {
		t.Fatal(err)
	}
	x, err := extractWith(b, "example.com/cgo.Add", defaultMaxFunctions, []string{"runtime.convT64"})
	if err != nil {
		t.Fatal(err)
	}
	var segs []string
	for _, s := range x.Segments {
		segs = append(segs, s.Name)
	}
	got := strings.Join(segs, " ")
	for _, want := range []string{"example.com/cgo.Add", "example.com/cgo._Cfunc_c_add.abi0", "_Cfunc_c_add", "c_add"} {
		if !strings.Contains(got, want) {
			t.Errorf("segments %q lack %q", got, want)
		}
	}
	ext := map[string]bool{}
	for _, s := range x.Stubs {
		if s.Kind == stubExternal {
			ext[s.Name] = true
		}
	}
	for _, n := range []string{"runtime.cgocall", "_cgo_topofstack", "runtime.cgoUse"} {
		if !ext[n] {
			t.Errorf("%s is not an external stub: %+v", n, x.Stubs)
		}
	}
	if !strings.Contains(string(x.Lean), "kind := .external") {
		t.Error("Extracted.lean has no external stub")
	}
	// a C symbol extracts directly
	c, err := extractWith(b, "c_sum", defaultMaxFunctions, nil)
	if err != nil || len(c.Segments) != 1 || c.Segments[0].Name != "c_sum" {
		t.Fatalf("c_sum: %v %+v", err, c)
	}
}

// ENDBR64 is one 4-byte instruction in the sweep (this x86asm version does not know it).
func TestSweepEndbr64(t *testing.T) {
	insts := sweepAmd64([]byte{0xF3, 0x0F, 0x1E, 0xFA, 0xC3}, 0x1000)
	if len(insts) != 2 || insts[0].Inst.Len != 4 || insts[1].PC != 0x1004 {
		t.Fatalf("sweep: %+v", insts)
	}
}
