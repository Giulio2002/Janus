package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The panic/defer/recover runtime functions (runtimePanicContractStubs) become pinned contracts
// when --contract names them, on both architectures: the extraction records them as pinned, and
// `janus check` regenerates and re-verifies the extraction.
func TestPanicContractExtraction(t *testing.T) {
	cases := []struct {
		sym       string
		contracts []string
		want      []string // contracts that must be recorded, pinned
	}{
		{"example.com/basic.DeferTwice", []string{"--contract", "runtime.deferproc*", "--contract", "runtime.deferreturn"},
			[]string{"runtime.deferproc", "runtime.deferreturn"}},
		{"example.com/basic.RecoverSet", []string{"--contract", "runtime.gopanic", "--contract", "runtime.gorecover",
			"--contract", "runtime.deferreturn", "--contract", "runtime.convT64"},
			[]string{"runtime.gopanic", "runtime.gorecover", "runtime.deferreturn"}},
	}
	for _, c := range cases {
		dir := mustExtract(t, c.sym, c.contracts...)
		id := readIdentity(t, dir)
		pinned := map[string]bool{}
		for _, ct := range id.Contracts {
			if ct.Pinned {
				pinned[ct.Name] = true
			}
		}
		for _, w := range c.want {
			if !pinned[w] {
				t.Errorf("%s: contract %s not recorded as pinned; contracts=%+v", c.sym, w, id.Contracts)
			}
		}
		if code, _, stderr := runJanus(t, "check", dir); code != 0 {
			t.Errorf("check %s failed: %s", c.sym, stderr)
		}
	}
}

// runtimePanicContractStubs is exactly the panic/defer/recover entry points the contract library
// (Janus/Contracts/Panic.lean) describes, and scripts/stubpins links every one so gen-stubpins
// measures (pins) it.
func TestPanicContractStubNames(t *testing.T) {
	if len(runtimePanicContractStubs) != 9 {
		t.Errorf("%d panic contract stubs, want 9", len(runtimePanicContractStubs))
	}
	for name := range runtimePanicContractStubs {
		short := strings.TrimPrefix(name, "runtime.")
		if len(stubPins["arm64"][name]) == 0 && !runtimePanicStubs[name] {
			t.Errorf("no arm64 pin for %s", name)
		}
		if len(stubPins["amd64"][name]) == 0 && !runtimePanicStubs[name] {
			t.Errorf("no amd64 pin for %s", name)
		}
		_ = short
	}
}

// On amd64 the pcsp table of a function with a frame pointer takes the value 8 in the prologue
// (after PUSHQ BP) and the epilogue, and the frame size in the body: the panic contracts' frame size
// is the body's, and the funcdata of an open-coded defer is read as on arm64.
func TestAmd64PanicFuncInfo(t *testing.T) {
	bin := exampleAmd64(t)
	cases := []struct {
		sym       string
		contracts []string
		want      []string
	}{
		{"example.com/basic.DeferTwice", []string{"--contract", "runtime.deferproc*", "--contract", "runtime.deferreturn"},
			[]string{`name := "example.com/basic.DeferTwice", entry := `, "frame := 24, deferreturn := 0x39"}},
		{"example.com/basic.RecoverSet", []string{"--contract", "runtime.gopanic", "--contract", "runtime.gorecover",
			"--contract", "runtime.deferreturn"},
			[]string{"frame := 64, deferreturn := 0x86", "openDefer := some (33, 8)"}},
	}
	for _, c := range cases {
		dir := filepath.Join(t.TempDir(), "art")
		code, _, stderr := runJanus(t, append([]string{"extract", bin, c.sym, dir}, c.contracts...)...)
		if code != 0 {
			t.Fatalf("extract %s failed: %s", c.sym, stderr)
		}
		b, err := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
		if err != nil {
			t.Fatal(err)
		}
		for _, w := range c.want {
			if !strings.Contains(string(b), w) {
				t.Errorf("%s: Extracted.lean lacks %q", c.sym, w)
			}
		}
	}
}
