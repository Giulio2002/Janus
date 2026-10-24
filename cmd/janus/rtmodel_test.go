package main

import (
	"encoding/binary"
	"os"
	"path/filepath"
	"testing"
)

// rt-model EX1 (docs/AUDIT-MODEL.md): the extractor copies code and read-only data by section
// header, but the kernel loads by program header (PT_LOAD) and ignores section headers. A
// binary whose `.text` section header points at a different file offset than the executable
// PT_LOAD maps still runs the real code, yet Janus would read (and prove about) the wrong
// bytes. validateSegments rejects such a section/segment disagreement.

// tamperTextOffset copies src to a temp file and advances the `.text` section header's file
// offset by delta, leaving every program header untouched (so the loaded image is unchanged).
func tamperTextOffset(t *testing.T, src string, delta uint64) string {
	t.Helper()
	data, err := os.ReadFile(src)
	if err != nil {
		t.Fatal(err)
	}
	// ELF64 little-endian header fields.
	eShoff := binary.LittleEndian.Uint64(data[0x28:])
	eShentsize := binary.LittleEndian.Uint16(data[0x3a:])
	eShnum := binary.LittleEndian.Uint16(data[0x3c:])
	eShstrndx := binary.LittleEndian.Uint16(data[0x3e:])
	shdr := func(i int) int { return int(eShoff) + i*int(eShentsize) }
	strOff := binary.LittleEndian.Uint64(data[shdr(int(eShstrndx))+24:])
	name := func(off uint32) string {
		b := data[strOff+uint64(off):]
		n := 0
		for n < len(b) && b[n] != 0 {
			n++
		}
		return string(b[:n])
	}
	found := false
	for i := 0; i < int(eShnum); i++ {
		o := shdr(i)
		if name(binary.LittleEndian.Uint32(data[o:])) == ".text" {
			cur := binary.LittleEndian.Uint64(data[o+24:])
			binary.LittleEndian.PutUint64(data[o+24:], cur+delta)
			found = true
			break
		}
	}
	if !found {
		t.Fatal("no .text section header")
	}
	dst := filepath.Join(t.TempDir(), "tampered")
	if err := os.WriteFile(dst, data, 0o755); err != nil {
		t.Fatal(err)
	}
	return dst
}

func TestSegmentMismatchRejected(t *testing.T) {
	// The untampered example binary must still load and extract.
	if _, err := loadBinary(exampleBin); err != nil {
		t.Fatalf("untampered example binary rejected: %v", err)
	}
	// A `.text` whose section header disagrees with its PT_LOAD must be rejected at load time.
	bad := tamperTextOffset(t, exampleBin, 0x40)
	if _, err := loadBinary(bad); err == nil {
		t.Fatal("binary with a section/segment mismatch was accepted (rt-model EX1)")
	} else if d, ok := err.(*diag); !ok || d.Stage != "binary validation" {
		t.Fatalf("expected a binary-validation diagnostic, got %v", err)
	}
	// And so must the extract path (which is what a user runs).
	out := filepath.Join(t.TempDir(), "art")
	if code, _, _ := runJanus(t, "extract", bad, "example.com/basic.Add", out); code == 0 {
		t.Fatal("extract accepted a binary with a section/segment mismatch (rt-model EX1)")
	}
}
