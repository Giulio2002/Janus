package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// --contract: a direct call to a matching function is not followed, the callee is recorded in
// Program.contracts and identity.json, and check regenerates it.
func TestContractExtraction(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.NewPair", "--contract", "runtime.new*", "--contract", "runtime.mallocgc")
	id := readIdentity(t, dir)
	if len(id.Functions) != 1 || id.Functions[0].Name != "example.com/basic.NewPair" {
		t.Fatalf("functions: %+v (the contract callee must not be followed)", id.Functions)
	}
	if len(id.Contracts) != 1 || id.Contracts[0].Name != "runtime.newobject" {
		t.Fatalf("contracts: %+v", id.Contracts)
	}
	if strings.Join(id.ContractPatterns, ",") != "runtime.new*,runtime.mallocgc" {
		t.Fatalf("patterns: %v", id.ContractPatterns)
	}
	lean, err := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if err != nil {
		t.Fatal(err)
	}
	want := `("runtime.newobject", ` + id.Contracts[0].Address + `)`
	if !strings.Contains(string(lean), "def contracts : List (String × Nat) := [\n  "+want+" ]") ||
		!strings.Contains(string(lean), "contracts := contracts }") {
		t.Fatalf("Extracted.lean lacks the contract list:\n%s", lean)
	}
	if code, out, stderr := runJanus(t, "check", dir); code != 0 || !strings.Contains(out, "Runtime contracts (not extracted): runtime.newobject @ ") {
		t.Fatalf("check: %d\n%s\n%s", code, out, stderr)
	}

	// The contract list is part of what check compares: dropping it from identity.json makes
	// check regenerate an extraction that follows newobject, which no longer matches.
	idPath := filepath.Join(dir, "identity.json")
	raw, _ := os.ReadFile(idPath)
	tampered := strings.Replace(string(raw), `"runtime.new*",`, ``, 1)
	tampered = strings.Replace(tampered, `"runtime.mallocgc"`, `"runtime.nomatch"`, 1)
	if err := os.WriteFile(idPath, []byte(tampered), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, _, stderr := runJanus(t, "check", dir); code == 0 || !strings.Contains(stderr, "Invalid") {
		t.Fatalf("check accepted a changed contract list: %s", stderr)
	}
}

// Without --contract nothing changes: no contract fields in the identity, no contract list in
// Extracted.lean (so earlier artifacts keep their bytes).
func TestNoContractUnchanged(t *testing.T) {
	dir := mustExtract(t, "example.com/basic.Add")
	raw, _ := os.ReadFile(filepath.Join(dir, "identity.json"))
	lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
	if strings.Contains(string(raw), "contract") || strings.Contains(string(lean), "contracts") {
		t.Fatalf("an extraction without --contract mentions contracts:\n%s\n%s", raw, lean)
	}
	if !strings.Contains(string(lean), "def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }\n") {
		t.Fatalf("program definition changed:\n%s", lean)
	}
}

func TestContractPatterns(t *testing.T) {
	m, err := newContractMatcher([]string{"runtime.gcWriteBarrier*", "runtime.?alloc"})
	if err != nil {
		t.Fatal(err)
	}
	for name, want := range map[string]bool{
		"runtime.gcWriteBarrier2":      true,
		"runtime.gcWriteBarrier2.abi0": true,
		"runtime.malloc":               true,
		"runtime.mallocgc":             false,
		"runtime/gcWriteBarrier":       false,
		"example.com/x.runtime.malloc": false,
	} {
		if got := m.match(name); got != want {
			t.Errorf("match(%q) = %v, want %v", name, got, want)
		}
	}
	if _, err := newContractMatcher([]string{""}); err == nil {
		t.Error("an empty pattern was accepted")
	}
	// The entry function cannot be a contract.
	if code, _, stderr := runJanus(t, "extract", exampleBin, "example.com/basic.Add", t.TempDir(), "--contract", "example.com/basic.*"); code == 0 ||
		!strings.Contains(stderr, "cannot be a contract") {
		t.Fatalf("entry matched by --contract was accepted: %s", stderr)
	}
}
