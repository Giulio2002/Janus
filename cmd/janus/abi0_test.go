package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// buildAsm builds examples/asm (Go assembly, ABI0) for linux/goarch.
func buildAsm(t *testing.T, goarch string) string {
	t.Helper()
	bin := filepath.Join(t.TempDir(), "examples-asm-"+goarch)
	cmd := exec.Command("go", "build", "-trimpath", "-o", bin, "./cmd")
	cmd.Dir = filepath.Join(repoRoot, "examples", "asm")
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH="+goarch, "GOAMD64=v1", "CGO_ENABLED=0")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("building the asm example: %v\n%s", err, out)
	}
	return bin
}

// The entry of an extraction is classified as Go assembly (ABI0), an ABI wrapper in either
// direction, or ordinary Go code (nothing recorded), on both ISAs; the extraction of a Go
// function with a direct ABI0 call contains the assembly body.
func TestEntryABI(t *testing.T) {
	for _, goarch := range []string{"arm64", "amd64"} {
		t.Run(goarch, func(t *testing.T) {
			b, err := loadBinary(buildAsm(t, goarch))
			if err != nil {
				t.Fatal(err)
			}
			cases := []struct{ sym, abi, source string }{
				{"example.com/asm.XorSlice.abi0", "ABI0", sourceAssembly},
				{"example.com/asm.Twice.abi0", "ABI0", sourceAssembly},
				{"example.com/asm.XorSlice", "ABIInternal", sourceABIWrapper},
				{"example.com/asm.double.abi0", "ABI0", sourceABIWrapper},
				{"example.com/asm.double", "", ""},
				{"example.com/asm.CallXor", "", ""},
			}
			for _, c := range cases {
				x, err := extractWith(b, c.sym, defaultMaxFunctions, nil)
				if err != nil {
					t.Fatalf("%s: %v", c.sym, err)
				}
				id := makeIdentity(x, "bin", defaultMaxFunctions)
				if id.EntryABI != c.abi || id.EntrySource != c.source {
					t.Errorf("%s: entry %q/%q, want %q/%q", c.sym, id.EntryABI, id.EntrySource, c.abi, c.source)
				}
				if c.abi == "" && strings.Contains(string(id.marshal()), "entryABI") {
					t.Errorf("%s: identity.json records an ABI for Go code", c.sym)
				}
			}
			// a direct ABI0 call from Go: the assembly body is extracted with its caller
			x, err := extractWith(b, "example.com/asm.CallXor", defaultMaxFunctions, nil)
			if err != nil {
				t.Fatal(err)
			}
			var names []string
			for _, s := range x.Segments {
				names = append(names, s.Name)
			}
			if !strings.Contains(strings.Join(names, " "), "example.com/asm.XorSlice.abi0") {
				t.Errorf("CallXor extraction lacks the ABI0 callee: %v", names)
			}
			// Twice.abi0 -> double.abi0 (ABI0->ABIInternal wrapper) -> double
			x, err = extractWith(b, "example.com/asm.Twice.abi0", defaultMaxFunctions, nil)
			if err != nil || len(x.Segments) != 3 {
				t.Fatalf("Twice.abi0: %v %d segments", err, len(x.Segments))
			}
			// an assembly function without a wrapper is found under its .abi0 name
			if _, err := b.lookup("internal/cpu.getMIDR"); goarch == "arm64" &&
				(err == nil || !strings.Contains(err.Error(), "internal/cpu.getMIDR.abi0 exists")) {
				t.Errorf("lookup hint: %v", err)
			}
		})
	}
}

// A statement using the other calling convention than the entry gets a warning.
func TestABIMismatch(t *testing.T) {
	abi0 := "Proof.correctness (x : BitVec 64) : Janus.GoABI0.Ensures0 Extracted.program Extracted.entry [x] 1 p q"
	internal := "Proof.correctness (x : BitVec 64) : Janus.Amd64.GoABI.Ensures Extracted.program Extracted.entry [x] p q"
	results := "Proof.correctness : Janus.GoABI.EnsuresResults Extracted.program Extracted.entry [x] 1 p q"
	for _, c := range []struct {
		stmt, symbol, recorded string
		warn                   bool
	}{
		{abi0, "f.abi0", "ABI0", false},
		{internal, "f.abi0", "ABI0", true},
		{results, "f.abi0", "", true},
		{abi0, "main.F", "", true},
		{internal, "main.F", "", false},
		{abi0, "f", "ABIInternal", true},
		{"Proof.correctness : Janus.GoABI.Summary Extracted.program 0 p q", "f.abi0", "ABI0", false},
		// round 10 A1: linked programs and a parenthesised entry are recognised too
		{"Proof.correctness (impl : List Janus.Segment) : Janus.GoABI0.Ensures0 (Extracted.program.link impl) Extracted.entry [x] 1 p q", "main.F", "", true},
		{"Proof.correctness : Janus.GoABI.Ensures (Extracted.program.withExit 4) (Extracted.entry) [x] p q", "f.abi0", "ABI0", true},
		{"Proof.correctness (impl : List Janus.Segment) : Janus.GoABI.Ensures (Extracted.program.link impl) Extracted.entry [x] p q", "main.F", "", false},
	} {
		got := abiMismatch(c.stmt, statementABI(c.symbol, c.recorded))
		if (got != "") != c.warn {
			t.Errorf("%q on %s (%s): warning %q, want %v", c.stmt, c.symbol, c.recorded, got, c.warn)
		}
	}
}
