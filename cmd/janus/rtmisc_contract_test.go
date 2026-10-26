package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The rtmisc contract stubs (rtmiscContractStubs: the -d=checkptr checks, the cgo pointer
// checks and the size-specialised allocator) are linked by scripts/stubpins (so gen-stubpins measures them) and
// described by their contract library.
func TestRtmiscContractStubNames(t *testing.T) {
	src, err := os.ReadFile(filepath.Join(repoRoot, "scripts", "stubpins", "main.go"))
	if err != nil {
		t.Fatal(err)
	}
	read := func(f string) string {
		b, err := os.ReadFile(filepath.Join(repoRoot, "Janus", "Contracts", f))
		if err != nil {
			t.Fatal(err)
		}
		return string(b)
	}
	checkptr, sc := read("InstrumentCalls.lean"), read("MallocSC.lean")
	if len(rtmiscContractStubs) != 70 {
		t.Errorf("%d rtmisc contract stubs, want 70", len(rtmiscContractStubs))
	}
	for name := range rtmiscContractStubs {
		if !strings.Contains(string(src), "//go:linkname s_"+strings.TrimPrefix(name, "runtime.")+" "+name+"\n") {
			t.Errorf("scripts/stubpins does not link %s", name)
		}
		short := strings.TrimPrefix(name, "runtime.")
		switch {
		case strings.HasPrefix(short, "checkptr"):
			if !strings.Contains(checkptr, "`"+short+"(") {
				t.Errorf("InstrumentCalls.lean does not describe %s", name)
			}
		case strings.HasPrefix(short, "cgoCheck"):
			if !strings.Contains(checkptr, "`runtime."+short+"(") {
				t.Errorf("InstrumentCalls.lean does not describe %s", name)
			}
		default:
			fam := strings.TrimRight(short, "0123456789")
			if !strings.Contains(sc, "`"+fam+"<") {
				t.Errorf("MallocSC.lean does not describe %s", name)
			}
		}
		if !runtimeContractStubs[name] {
			t.Errorf("%s is not in runtimeContractStubs", name)
		}
	}
}
