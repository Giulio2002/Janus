package main

import (
	"bytes"
	"debug/elf"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Round 8 G3: runtime stubs are pinned to their code (stubpin.go, stubpins_gen.go).

func loadT(t *testing.T, path string) *Binary {
	t.Helper()
	b, err := loadBinary(path)
	if err != nil {
		t.Fatal(err)
	}
	return b
}

func funcNamed(t *testing.T, b *Binary, name string) Func {
	t.Helper()
	f, err := b.lookup(name)
	if err != nil {
		t.Fatal(err)
	}
	return f
}

// Every stub of the honest example binaries (go1.26.0, both architectures) passes, whatever
// Go version build info claims: the decision does not read it.
func TestStubPinHonest(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		b := loadT(t, bin)
		n := 0
		for _, f := range b.Funcs {
			want, isStub := stubKind(f.Name)
			if !isStub {
				continue
			}
			n++
			for _, ver := range []string{"go1.26.0", "go1.27.0", "go1.25.5", "devel"} {
				b.GoVersion = ver
				b.stubCache = nil
				if k, ok, err := b.classifyStub(f); err != nil || !ok || k != want {
					t.Errorf("%s %s (build info %s): kind=%v ok=%v err=%v", b.GOARCH, f.Name, ver, k, ok, err)
				}
			}
		}
		if n < 10 {
			t.Errorf("%s: only %d stubs in the example binary", b.GOARCH, n)
		}
		for _, h := range []string{"runtime.panicCheck2", "runtime.throw"} {
			if !stubPinHelpers[h] || len(stubPins[b.GOARCH][h]) == 0 {
				t.Errorf("%s: helper %s not pinned", b.GOARCH, h)
			}
		}
	}
}

// One changed byte, in a stub or in a helper it calls, and the target is no longer a stub: an
// error, not a stub and not code.
func TestStubPinModifiedByte(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		for _, c := range []struct{ stub, patch string }{
			{"runtime.panicdivide", "runtime.panicdivide"},
			{"runtime.panicdivide", "runtime.panicCheck2"}, // a pinned helper the stub calls
			{"runtime.gopanic", "runtime.gopanic"},
			{"runtime.panicBounds", "runtime.panicBounds64"}, // a stub the stub tail-calls
		} {
			b := loadT(t, bin)
			f, p := funcNamed(t, b, c.stub), funcNamed(t, b, c.patch)
			if _, ok, err := b.classifyStub(f); err != nil || !ok {
				t.Fatalf("%s %s before the patch: ok=%v err=%v", b.GOARCH, c.stub, ok, err)
			}
			// a byte of the stack-check prologue (not a masked field): the frame-size or
			// register byte of its first instruction
			off := p.Addr - b.textAddr + 1
			b.text[off] ^= 0x01
			b.stubCache = nil
			_, ok, err := b.classifyStub(f)
			if err == nil || ok {
				t.Errorf("%s %s with a byte of %s changed: ok=%v err=%v", b.GOARCH, c.stub, c.patch, ok, err)
				continue
			}
			if !strings.Contains(err.Error(), "is not the Go runtime's "+c.stub) {
				t.Errorf("%s %s: unexpected message: %v", b.GOARCH, c.stub, err)
			}
		}
	}
}

// A call retargeted to another function (a masked field, so the code bytes still match) changes
// the recorded symbol identity, and fails.
func TestStubPinRetargetedCall(t *testing.T) {
	b := loadT(t, exampleBin)
	f := funcNamed(t, b, "runtime.panicdivide")
	ws, _ := b.words(f)
	other := funcNamed(t, b, "runtime.panicshift")
	for i, w := range ws {
		if w&0xFC000000 == 0x94000000 { // the first BL (to panicCheck2)
			pc := f.Addr + 4*uint64(i)
			nw := 0x94000000 | uint32((int64(other.Addr)-int64(pc))/4)&0x03FFFFFF
			off := pc - b.textAddr
			b.text[off], b.text[off+1], b.text[off+2], b.text[off+3] = byte(nw), byte(nw>>8), byte(nw>>16), byte(nw>>24)
			break
		}
	}
	if _, ok, err := b.classifyStub(f); err == nil || ok {
		t.Fatalf("retargeted call: ok=%v err=%v", ok, err)
	}
}

// The pclntab must place the stub in package runtime's file the pins record: the same code in
// a file of another directory fails.
func TestStubPinWrongPclntabFile(t *testing.T) {
	for _, bin := range []string{exampleBin, exampleAmd64(t)} {
		b := loadT(t, bin)
		f := funcNamed(t, b, "runtime.panicdivide")
		patched := 0
		for i := range b.sections {
			if b.sections[i].Name == ".gopclntab" {
				d := b.sections[i].data
				patched = bytes.Count(d, []byte("runtime/panic.go"))
				copy(d, bytes.ReplaceAll(d, []byte("runtime/panic.go"), []byte("runtimX/panic.go")))
			}
		}
		if patched == 0 {
			t.Fatalf("%s: no runtime/panic.go in the pclntab", b.GOARCH)
		}
		_, ok, err := b.classifyStub(f)
		if err == nil || ok || !strings.Contains(err.Error(), `in file "runtimX/panic.go"`) {
			t.Errorf("%s: wrong pclntab file: ok=%v err=%v", b.GOARCH, ok, err)
		}
	}
}

// End to end: extraction of Div from a binary whose runtime.panicdivide has one byte changed
// fails with the round-8 message (and so does verification, which re-extracts).
func TestStubPinExtractRejects(t *testing.T) {
	data, err := os.ReadFile(exampleBin)
	if err != nil {
		t.Fatal(err)
	}
	ef, err := elf.NewFile(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	b := loadT(t, exampleBin)
	f := funcNamed(t, b, "runtime.panicdivide")
	text := ef.Section(".text")
	data[text.Offset+(f.Addr-text.Addr)+1] ^= 0x01
	bad := filepath.Join(t.TempDir(), "patched")
	if err := os.WriteFile(bad, data, 0o755); err != nil {
		t.Fatal(err)
	}
	code, _, stderr := runJanus(t, "extract", bad, "example.com/basic.Div", filepath.Join(t.TempDir(), "x"))
	if code == 0 || !strings.Contains(stderr, "is not the Go runtime's runtime.panicdivide") || !strings.Contains(stderr, "round 8 G3") {
		t.Errorf("extract of a patched stub: code %d\n%s", code, stderr)
	}
}
