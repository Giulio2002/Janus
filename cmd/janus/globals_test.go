package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// --global copies the link-time image of writable package variables into Program.globals
// (globals.go): .noptrdata bytes, .noptrbss zero, recorded in identity.json, and checked by
// janus check like the rest of the extraction.
func TestGlobalExtraction(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.MulAlgo",
		"--global", "example.com/basic.karatsubaCut", "--global", "example.com/basic.mulBias")
	id := readIdentity(t, dir)
	if len(id.Globals) != 2 || len(id.GlobalPatterns) != 2 {
		t.Fatalf("globals %+v, patterns %v", id.Globals, id.GlobalPatterns)
	}
	byName := map[string]identityGlobal{}
	for _, g := range id.Globals {
		byName[g.Name] = g
	}
	cut, bias := byName["example.com/basic.karatsubaCut"], byName["example.com/basic.mulBias"]
	if cut.Section != ".noptrdata" || cut.Size != 8 || cut.Sha256 == "" {
		t.Errorf("karatsubaCut: %+v", cut)
	}
	if bias.Section != ".noptrbss" || bias.Size != 8 || bias.Sha256 != "" {
		t.Errorf("mulBias (zero at load, no file bytes): %+v", bias)
	}
	lean, err := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"globals := globals", `name := "example.com/basic.karatsubaCut"`,
		"size := 8, init := [0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]", `name := "example.com/basic.mulBias"`,
		"size := 8, init := [] }"} {
		if !strings.Contains(string(lean), want) {
			t.Errorf("Extracted.lean lacks %q", want)
		}
	}
	if code, out, stderr := runJanus(t, "check", dir); code != 0 || !strings.Contains(out, "Writable globals (link-time images)") {
		t.Fatalf("check: %d %s %s", code, out, stderr)
	}
	// a changed image is caught by check (the bytes are part of Extracted.lean)
	tampered := strings.Replace(string(lean), "init := [0x28,", "init := [0x29,", 1)
	if err := os.WriteFile(filepath.Join(dir, "Extracted.lean"), []byte(tampered), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, _, _ := runJanus(t, "check", dir); code == 0 {
		t.Fatal("check accepted a tampered global image")
	}
}

// Without --global the extraction is byte-identical to one made before globals existed.
func TestGlobalNoneUnchanged(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.MulAlgo")
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if strings.Contains(string(lean), "globals") {
		t.Error("Extracted.lean mentions globals without --global")
	}
	raw, _ := os.ReadFile(filepath.Join(dir, "identity.json"))
	if strings.Contains(string(raw), "global") {
		t.Error("identity.json mentions globals without --global")
	}
}

// A pointer chain copies the anonymous static object a pointer global points to.
func TestGlobalPointerChain(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.TuningCut", "--global", "example.com/basic.tuning->16")
	id := readIdentity(t, dir)
	if len(id.Globals) != 2 {
		t.Fatalf("globals %+v", id.Globals)
	}
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	// Tuning{Cut: 32, Bias: 7}
	want := "size := 16, init := [0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]"
	if !strings.Contains(string(lean), `name := "example.com/basic.tuning->16"`) || !strings.Contains(string(lean), want) {
		t.Errorf("Extracted.lean lacks the pointee image:\n%s", lean)
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check: %s", stderr)
	}
}

func TestGlobalErrors(t *testing.T) {
	b, err := loadBinary(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	var ro string
	for _, d := range b.dataSyms {
		if sec, ok := b.sectionOf(d.Addr); ok && !sec.Writable && !sec.Exec && !sec.NoBits && d.Addr+d.Size <= sec.End() {
			ro = d.Name
			break
		}
	}
	if ro == "" {
		t.Fatal("no read-only data symbol in the example binary")
	}
	cases := []struct{ pat, want string }{
		{"example.com/basic.noSuchVar", "matches no data symbol"},
		{ro, "read-only section"},
		{"example.com/basic.mulBias->8", "is nil in the link-time image"},
		{"example.com/basic.tuning+16->8", "leaves no 8-byte pointer"},
		{"example.com/basic.tuning->0", "positive size"},
		{"example.com/basic.tun*->8", "not a glob"},
	}
	for _, c := range cases {
		dir := filepath.Join(t.TempDir(), "art")
		code, _, stderr := runJanus(t, "extract", exampleBin, "example.com/basic.MulAlgo", dir, "--global", c.pat)
		if code == 0 || !strings.Contains(stderr, c.want) {
			t.Errorf("--global %q: exit %d, want an error containing %q, got %s", c.pat, code, c.want, stderr)
		}
	}
}

func TestParseGlobalPattern(t *testing.T) {
	cases := []struct {
		in    string
		base  string
		steps []globalStep
	}{
		{"math/big.intOne", "math/big.intOne", nil},
		{"math/big.*Threshold", "math/big.*Threshold", nil},
		{"math/big.intOne->32", "math/big.intOne", []globalStep{{0, 32, "->32"}}},
		{"math/big.intOne->32+8->8", "math/big.intOne", []globalStep{{0, 32, "->32"}, {8, 8, "+8->8"}}},
		{"p.v+0x10->0x20", "p.v", []globalStep{{16, 32, "+0x10->0x20"}}},
	}
	for _, c := range cases {
		base, steps, err := parseGlobalPattern(c.in)
		if err != nil || base != c.base || len(steps) != len(c.steps) {
			t.Errorf("%q: %q %+v %v", c.in, base, steps, err)
			continue
		}
		for i := range steps {
			if steps[i] != c.steps[i] {
				t.Errorf("%q step %d: %+v, want %+v", c.in, i, steps[i], c.steps[i])
			}
		}
	}
	for _, bad := range []string{"x->", "x->y", "x+1->", "x->8junk"} {
		if _, _, err := parseGlobalPattern(bad); err == nil {
			t.Errorf("%q: no error", bad)
		}
	}
}

// The runtime's own writable globals: runtime.zerobase and runtime.writeBarrier (zero-filled
// .noptrbss in the image) and the CPU-feature table internal/cpu.ARM64, which startup code
// overwrites; the image is recorded, and a theorem about them quantifies over their values
// (GlobalIs) rather than assuming it.
func TestGlobalRuntimeVars(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.MulAlgo",
		"--global", "runtime.zerobase", "--global", "runtime.writeBarrier", "--global", "internal/cpu.ARM64")
	id := readIdentity(t, dir)
	if len(id.Globals) != 3 {
		t.Fatalf("globals %+v", id.Globals)
	}
	for _, g := range id.Globals {
		if g.Section != ".noptrbss" || g.Sha256 != "" || g.Size == 0 {
			t.Errorf("%s: %+v (zero at load, no file bytes)", g.Name, g)
		}
	}
	if code, _, stderr := runJanus(t, "check", dir); code != 0 {
		t.Fatalf("check: %s", stderr)
	}
}
