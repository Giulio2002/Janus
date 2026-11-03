package main

import (
	"bytes"
	"debug/elf"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// elfSymbol looks a symbol up in the binary's ELF symbol table, independently of Binary.
func elfSymbol(t *testing.T, bin, name string) elf.Symbol {
	t.Helper()
	f, err := elf.Open(bin)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	syms, err := f.Symbols()
	if err != nil {
		t.Fatal(err)
	}
	for _, s := range syms {
		if s.Name == name {
			return s
		}
	}
	t.Fatalf("no symbol %s in %s", name, bin)
	return elf.Symbol{}
}

// TestDataSymConstants: Extracted.lean names the address and size of every data symbol the code
// references, on both ISAs, with the values of the ELF symbol table; the constants are covered by
// `janus check`.
func TestDataSymConstants(t *testing.T) {
	bins := map[string]string{"arm64": exampleBin, "amd64": exampleAmd64(t)}
	for arch, bin := range bins {
		cases := []struct{ fn, sym, section string }{
			{"SymPows", "example.com/basic.symPows", ".noptrdata"},
			{"GlobalTable", "example.com/basic.tbl", ".noptrdata"},
			{"Bump", "example.com/basic.counter", ".noptrbss"},
		}
		for _, c := range cases {
			dir := filepath.Join(t.TempDir(), arch+c.fn)
			if code, _, stderr := runJanus(t, "extract", bin, "example.com/basic."+c.fn, dir); code != 0 {
				t.Fatalf("%s %s: %s", arch, c.fn, stderr)
			}
			lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
			s := elfSymbol(t, bin, c.sym)
			wantA := fmt.Sprintf("def dataAddr.«%s» : Nat := 0x%x\n", c.sym, s.Value)
			wantS := fmt.Sprintf("def dataSize.«%s» : Nat := %d\n", c.sym, s.Size)
			doc := fmt.Sprintf("/-- `%s` (%s, %d bytes) -/\n", c.sym, c.section, s.Size)
			for _, w := range []string{wantA, wantS, doc} {
				if !strings.Contains(string(lean), w) {
					t.Errorf("%s %s: Extracted.lean lacks %q:\n%s", arch, c.fn, w, lean)
				}
			}
			if code, _, stderr := runJanus(t, "check", dir); code != 0 {
				t.Fatalf("%s %s: check: %s", arch, c.fn, stderr)
			}
		}
	}
}

// TestDataSymNone: a function that references no named data symbol (Add) and one whose constant
// is an anonymous read-only static (Table) get no constants, so those extractions are
// byte-identical to the earlier format.
func TestDataSymNone(t *testing.T) {
	for arch, bin := range map[string]string{"arm64": exampleBin, "amd64": exampleAmd64(t)} {
		for _, fn := range []string{"Add", "Table"} {
			dir := filepath.Join(t.TempDir(), arch+fn)
			if code, _, stderr := runJanus(t, "extract", bin, "example.com/basic."+fn, dir); code != 0 {
				t.Fatalf("%s %s: %s", arch, fn, stderr)
			}
			lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
			if bytes.Contains(lean, []byte("dataAddr")) || bytes.Contains(lean, []byte("dataSize")) {
				t.Errorf("%s %s: unexpected data symbol constants", arch, fn)
			}
		}
	}
}

// TestDataSymTypeDescriptor: a type descriptor, which has no ELF symbol, is named
// "type:<type string>#<hash>" from the descriptor and gets an address but no size.
func TestDataSymTypeDescriptor(t *testing.T) {
	re := regexp.MustCompile(`(?m)^def dataAddr\.«(type:basic\.Pair#[0-9a-f]{8})» : Nat := 0x([0-9a-f]+)$`)
	for arch, bin := range map[string]string{"arm64": exampleBin, "amd64": exampleAmd64(t)} {
		dir := filepath.Join(t.TempDir(), arch)
		if code, _, stderr := runJanus(t, "extract", bin, "example.com/basic.NewPair", dir, "--contract", "runtime.newobject"); code != 0 {
			t.Fatalf("%s: %s", arch, stderr)
		}
		lean, _ := os.ReadFile(filepath.Join(dir, "Extracted.lean"))
		m := re.FindStringSubmatch(string(lean))
		if m == nil {
			t.Fatalf("%s: no type descriptor constant:\n%s", arch, lean)
		}
		if strings.Contains(string(lean), "dataSize.«"+m[1]) {
			t.Errorf("%s: a type descriptor must not get a size", arch)
		}
		// the address is the descriptor the code computes: a copied data object starts there
		if !strings.Contains(string(lean), "base := 0x"+m[2]) {
			t.Errorf("%s: no data object at the descriptor 0x%s", arch, m[2])
		}
	}
}

// TestDataSymTamper: a changed constant is rejected by `janus check`, even when the recorded
// hash of Extracted.lean is changed to match (the file is regenerated from the binary).
func TestDataSymTamper(t *testing.T) {
	for arch, bin := range map[string]string{"arm64": exampleBin, "amd64": exampleAmd64(t)} {
		dir := filepath.Join(t.TempDir(), arch)
		if code, _, stderr := runJanus(t, "extract", bin, "example.com/basic.SymPows", dir); code != 0 {
			t.Fatalf("%s: %s", arch, stderr)
		}
		leanPath, idPath := filepath.Join(dir, "Extracted.lean"), filepath.Join(dir, "identity.json")
		orig, _ := os.ReadFile(leanPath)
		origID, _ := os.ReadFile(idPath)
		for _, c := range []struct{ name, from, to string }{
			{"address", "dataAddr.«example.com/basic.symPows» : Nat := 0x", "dataAddr.«example.com/basic.symPows» : Nat := 0x1"},
			{"size", "dataSize.«example.com/basic.symPows» : Nat := 64", "dataSize.«example.com/basic.symPows» : Nat := 65"},
		} {
			forged := bytes.Replace(orig, []byte(c.from), []byte(c.to), 1)
			if bytes.Equal(forged, orig) {
				t.Fatalf("%s %s: pattern not found", arch, c.name)
			}
			os.WriteFile(leanPath, forged, 0o644)
			os.WriteFile(idPath, bytes.Replace(origID, []byte(sha256Hex(orig)), []byte(sha256Hex(forged)), 1), 0o644)
			code, _, stderr := runJanus(t, "check", dir)
			if code != 1 || !strings.Contains(stderr, "differs from the regenerated extraction") {
				t.Errorf("%s: forged %s accepted: %d %s", arch, c.name, code, stderr)
			}
			// and without fixing the recorded hash
			os.WriteFile(idPath, origID, 0o644)
			if code, _, stderr := runJanus(t, "check", dir); code != 1 || !strings.Contains(stderr, "modified after extraction") {
				t.Errorf("%s: forged %s (hash kept) accepted: %d %s", arch, c.name, code, stderr)
			}
		}
		os.WriteFile(leanPath, orig, 0o644)
		os.WriteFile(idPath, origID, 0o644)
	}
}

// TestDataSymNaming: identifiers are unique and valid Lean whatever the symbol names are.
func TestDataSymNaming(t *testing.T) {
	b := &Binary{
		sections: []section{{Name: ".data", Addr: 0x1000, Size: 0x1000, Writable: true, data: make([]byte, 0x1000)}},
		dataSyms: []Func{
			{Name: "p.dup", Addr: 0x1000, Size: 8},
			{Name: "p.dup", Addr: 0x1010, Size: 8},
			{Name: "p.bad»name", Addr: 0x1020, Size: 8},
			{Name: "p.cmt-/x", Addr: 0x1030, Size: 8},
			{Name: "sym@0x1030", Addr: 0x1040, Size: 8},
			{Name: "p.ok", Addr: 0x1050, Size: 8},
		},
	}
	x := &Extraction{Bin: b}
	for _, a := range []uint64{0x1000, 0x1010, 0x1020, 0x1030, 0x1040, 0x1050, 0x1054, 0x1000} {
		x.DataRefs = append(x.DataRefs, DataRef{From: 1, Target: a, Kind: "adr"})
	}
	syms := collectDataSyms(x)
	if len(syms) != 6 {
		t.Fatalf("want 6 symbols, got %+v", syms)
	}
	seen := map[string]bool{}
	want := map[uint64]string{0x1000: "sym@0x1000", 0x1010: "sym@0x1010", 0x1020: "sym@0x1020", 0x1030: "sym@0x1030", 0x1050: "p.ok"}
	for _, d := range syms {
		if seen[d.Ident] || !leanIdentOK(d.Ident) {
			t.Errorf("identifier %q duplicated or invalid", d.Ident)
		}
		seen[d.Ident] = true
		if w, ok := want[d.Addr]; ok && d.Ident != w {
			t.Errorf("0x%x: identifier %q, want %q", d.Addr, d.Ident, w)
		}
	}
	var sb strings.Builder
	writeDataSyms(&sb, syms)
	out := sb.String()
	if strings.Count(out, "def dataAddr.") != 6 || strings.Count(out, "def dataSize.") != 6 || strings.Contains(out, "»name") {
		t.Errorf("unexpected rendering:\n%s", out)
	}
}
