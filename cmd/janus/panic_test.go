package main

import (
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
	if len(runtimePanicContractStubs) != 8 {
		t.Errorf("%d panic contract stubs, want 8", len(runtimePanicContractStubs))
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
