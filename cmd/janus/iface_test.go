package main

import (
	"bytes"
	"debug/elf"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// The interface runtime contracts (Janus/Contracts/Iface.lean): a --contract on one of
// runtimeContractStubs is pinned to the runtime's code, like a stub (stubpin.go).

// Every interface runtime function of the honest example binaries passes the pin, on both
// architectures.
func TestContractPinHonest(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		b := loadT(t, bin)
		n := 0
		for _, f := range b.Funcs {
			if !runtimeContractStubs[f.Name] {
				continue
			}
			n++
			if err := b.checkContractPin(f); err != nil {
				t.Errorf("%s %s: %v", b.GOARCH, f.Name, err)
			}
		}
		// the examples call convT64, typeAssert, interfaceSwitch, efaceeq (and std links more)
		if n < 4 {
			t.Errorf("%s: only %d interface runtime functions in the example binary", b.GOARCH, n)
		}
		for _, name := range []string{"runtime.convT64", "runtime.typeAssert", "runtime.interfaceSwitch", "runtime.efaceeq"} {
			if len(stubPins[b.GOARCH][name]) == 0 {
				t.Errorf("%s: %s has no pinned code", b.GOARCH, name)
			}
		}
	}
}

// The examples' extractions record the pinned contract, check regenerates it, and the report
// marks it pinned; a contract outside the list (newobject) is not marked.
func TestContractPinRecorded(t *testing.T) {
	for _, c := range []struct{ sym, contract string }{
		{"example.com/basic.Box", "runtime.convT64"},
		{"example.com/basic.AsHasher", "runtime.typeAssert"},
		{"example.com/basic.Classify", "runtime.interfaceSwitch"},
		{"example.com/basic.Equal", "runtime.efaceeq"},
	} {
		dir := mustExtract(t, c.sym, "--contract", c.contract)
		id := readIdentity(t, dir)
		if len(id.Contracts) != 1 || id.Contracts[0].Name != c.contract || !id.Contracts[0].Pinned {
			t.Fatalf("%s: contracts %+v", c.sym, id.Contracts)
		}
		if code, out, stderr := runJanus(t, "check", dir); code != 0 ||
			!strings.Contains(out, c.contract+" @ "+id.Contracts[0].Address+" (pinned)") {
			t.Fatalf("check %s: %d\n%s\n%s", c.sym, code, out, stderr)
		}
	}
	dir := mustExtract(t, "example.com/basic.NewPair", "--contract", "runtime.newobject")
	raw, _ := os.ReadFile(filepath.Join(dir, "identity.json"))
	if strings.Contains(string(raw), "pinned") {
		t.Fatalf("an unpinned contract is marked pinned:\n%s", raw)
	}
}

// One changed byte in runtime.convT64 (a byte of its stack check, not a masked field): the
// extraction of Box with --contract runtime.convT64 fails, so no theorem can state a contract
// about a function that is not the runtime's. Without the --contract the same binary still
// extracts (the function is then simply code, followed and copied).
func TestContractPinRejectsModified(t *testing.T) {
	data, err := os.ReadFile(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	ef, err := elf.NewFile(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	b := loadT(t, exampleBin)
	f := funcNamed(t, b, "runtime.convT64")
	text := ef.Section(".text")
	data[text.Offset+(f.Addr-text.Addr)+1] ^= 0x01
	bad := filepath.Join(t.TempDir(), "patched")
	if err := os.WriteFile(bad, data, 0o755); err != nil {
		t.Fatal(err)
	}
	code, _, stderr := runJanus(t, "extract", bad, "example.com/basic.Box", filepath.Join(t.TempDir(), "x"),
		"--contract", "runtime.convT64")
	if code == 0 || !strings.Contains(stderr, "is not the Go runtime's runtime.convT64") {
		t.Errorf("extract with a patched convT64 contract: code %d\n%s", code, stderr)
	}
	pb := loadT(t, bad)
	if err := pb.checkContractPin(funcNamed(t, pb, "runtime.convT64")); err == nil {
		t.Errorf("checkContractPin accepted a patched convT64")
	}
}

// The pin needs the pclntab to place the function in package runtime: a function of another
// package with the same code is not the runtime's (checked through the shared stub check).
func TestContractPinNeedsRuntimeFile(t *testing.T) {
	b := loadT(t, exampleBin)
	f := funcNamed(t, b, "runtime.efaceeq")
	patched := 0
	for i := range b.sections {
		if b.sections[i].Name == ".gopclntab" {
			d := b.sections[i].data
			patched = bytes.Count(d, []byte("runtime/alg.go"))
			copy(d, bytes.ReplaceAll(d, []byte("runtime/alg.go"), []byte("runtimX/alg.go")))
		}
	}
	if patched == 0 {
		t.Fatal("no runtime/alg.go in the pclntab")
	}
	if err := b.checkContractPin(f); err == nil || !strings.Contains(err.Error(), `in file "runtimX/alg.go"`) {
		t.Errorf("wrong pclntab file: %v", err)
	}
}

// The names of the list are the interface runtime entry points of docs/COVERAGE.md and of the
// contract library, and scripts/stubpins links every one (so gen-stubpins measures them).
func TestContractStubNames(t *testing.T) {
	src, err := os.ReadFile(filepath.Join(repoRoot, "scripts", "stubpins", "main.go"))
	if err != nil {
		t.Fatal(err)
	}
	lean, err := os.ReadFile(filepath.Join(repoRoot, "Janus", "Contracts", "Iface.lean"))
	if err != nil {
		t.Fatal(err)
	}
	if len(runtimeContractStubs) != 13+len(rtmiscContractStubs) {
		t.Errorf("%d contract stubs, want 13 interface ones and %d rtmisc ones", len(runtimeContractStubs), len(rtmiscContractStubs))
	}
	for name := range runtimeContractStubs {
		if rtmiscContractStubs[name] {
			continue // checked by TestRtmiscContractStubNames
		}
		if !strings.Contains(string(src), "//go:linkname s_"+strings.TrimPrefix(name, "runtime.")+" "+name+"\n") {
			t.Errorf("scripts/stubpins does not link %s", name)
		}
		if !strings.Contains(string(lean), "`"+strings.TrimPrefix(name, "runtime.")+"(") {
			t.Errorf("Janus/Contracts/Iface.lean does not describe %s", name)
		}
	}
}
