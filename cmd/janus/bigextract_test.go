package main

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
	"time"
)

// syntheticAmd64 is an amd64 extraction of the given code segment sizes (bytes), without a binary.
func syntheticAmd64(sizes []int) *Extraction {
	x := &Extraction{Bin: &Binary{MainModule: "example.com/big", GoVersion: "go1.26.0", GOOS: "linux", GOARCH: "amd64"},
		Entry: Func{Name: "example.com/big.F", Addr: 0x400000}}
	base := uint64(0x400000)
	for i, n := range sizes {
		bs := make([]byte, n)
		for j := range bs {
			bs[j] = byte(j*7 + i)
		}
		x.Segments = append(x.Segments, Segment{Name: fmt.Sprintf("example.com/big.F%d", i), Base: base, Size: uint64(n), Bytes: bs})
		base += uint64(n+15) &^ 15
	}
	return x
}

// TestRenderLargeAmd64 checks the shape of a large amd64 Extracted.lean: no list literal has more than treeListElems
// elements, a segment longer than that is a tree of definitions joined by `++` with at most treeFanout operands per
// node (so the nesting stays shallow), and the small and the mid-size shapes are unchanged. Without -short, and when
// `lake env lean` is available in the repository, the files elaborate (U-BIGEXTRACT: 6.9 KB of code in one inline
// `segments` literal hit maxRecDepth; one 41 KB segment timed out on heartbeats) in time linear in their size.
func TestRenderLargeAmd64(t *testing.T) {
	small := string(renderLeanAmd64(syntheticAmd64([]int{300, 400})))
	if !strings.Contains(small, "def segments : List Amd64.Segment := [\n  { name := ") {
		t.Errorf("small program is no longer inline:\n%s", small[:400])
	}
	edge := string(renderLeanAmd64(syntheticAmd64([]int{2048, 2048, 1024})))
	if !strings.Contains(edge, "def segments : List Amd64.Segment := [\n  { name := ") {
		t.Errorf("a 5120-byte program is still inline (as before):\n%.300s", edge)
	}
	mid := string(renderLeanAmd64(syntheticAmd64([]int{1500, 1700, 1763, 1900, 800})))
	if strings.Contains(mid, "def segments : List Amd64.Segment := [\n  { name := ") ||
		!strings.Contains(mid, "def seg0 : Amd64.Segment :=") || strings.Contains(mid, "set_option maxRecDepth 100000 in\ndef seg0 :") {
		t.Errorf("mid-size program (7.6 KB total) should be one definition per segment (segments up to 4096 bytes need no extra recursion depth):\n%.600s", mid)
	}
	huge := string(renderLeanAmd64(syntheticAmd64([]int{41466, 5000, 300})))
	for _, want := range []string{"def seg0_bytes_0 : List Nat :=", "def seg0_bytes_n0_0 : List Nat :=", "def seg0_bytes : List Nat :=",
		"def seg0 : Amd64.Segment :=\n  { name := \"example.com/big.F0\", base := 0x400000, bytes := seg0_bytes }", "def seg2 : Amd64.Segment :=\n  { name := \"example.com/big.F2\", base := 0x"} {
		if !strings.Contains(huge, want) {
			t.Errorf("large program lacks %q", want)
		}
	}
	if strings.Contains(huge, "set_option maxRecDepth 100000 in\ndef seg0 :") {
		t.Errorf("a tree-shaped segment needs no maxRecDepth")
	}
	if !strings.Contains(huge, "set_option maxRecDepth 100000 in\ndef seg1 :") || strings.Contains(huge, "def seg1_bytes") {
		t.Errorf("a 5000-byte segment keeps the earlier shape: one literal with a raised maxRecDepth")
	}
	// every list literal is short; every `++` node has at most treeFanout operands
	for _, m := range regexp.MustCompile(`(?s)def seg\d+_bytes\w*? : List Nat :=\n  (\[[^\]]*\]|[^\n]*)`).FindAllStringSubmatch(huge, -1) {
		if strings.HasPrefix(m[1], "[") {
			if n := strings.Count(m[1], "0x"); n > treeLeafElems {
				t.Errorf("a leaf has %d elements (> %d)", n, treeLeafElems)
			}
		} else if n := strings.Count(m[1], " ++ ") + 1; n > treeFanout {
			t.Errorf("a node has %d operands (> %d)", n, treeFanout)
		}
	}
	if testing.Short() {
		return
	}
	lake, err := findLake()
	if err != nil {
		t.Skip("lake not installed")
	}
	_ = lake
	for _, tc := range []struct {
		name  string
		sizes []int
	}{{"edge", []int{2048, 2048, 1024}}, {"mid", []int{1500, 1700, 1763, 1900, 800}}, {"huge", []int{41466, 5000, 300}}, {"many", func() []int {
		var s []int
		for i := 0; i < 60; i++ {
			s = append(s, 1700)
		}
		return s
	}()}} {
		dir := t.TempDir()
		if err := os.WriteFile(filepath.Join(dir, "Extracted.lean"), renderLeanAmd64(syntheticAmd64(tc.sizes)), 0o644); err != nil {
			t.Fatal(err)
		}
		cmd := exec.Command("lake", "env", "lean", filepath.Join(dir, "Extracted.lean"))
		cmd.Dir = repoRoot
		start := time.Now()
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("%s: Extracted.lean does not elaborate: %v\n%.2000s", tc.name, err, out)
		}
		t.Logf("%s: %v", tc.name, time.Since(start))
	}
}

// TestRenderLargeArm64AndData: the same for arm64 words, for large read-only data objects and for large globals.
func TestRenderLargeArm64AndData(t *testing.T) {
	x := &Extraction{Bin: &Binary{MainModule: "example.com/big", GoVersion: "go1.26.0", GOOS: "linux", GOARCH: "arm64"},
		Entry: Func{Name: "example.com/big.F", Addr: 0x400000}}
	base := uint64(0x400000)
	for i, n := range []int{40000, 700, 100} {
		ws := make([]uint32, n)
		for j := range ws {
			ws[j] = uint32(0xd503201f + j + i)
		}
		x.Segments = append(x.Segments, Segment{Name: fmt.Sprintf("example.com/big.F%d", i), Base: base, Size: uint64(4 * n), Words: ws})
		base += uint64(4*n+15) &^ 15
	}
	big := make([]byte, 30000)
	for i := range big {
		big[i] = byte(i * 3)
	}
	x.Data = []DataSeg{{Name: ".rodata+0x0", Base: 0x500000, Bytes: big, Section: ".rodata"}, {Name: ".rodata+0x9000", Base: 0x509000, Bytes: big[:200], Section: ".rodata"}}
	x.Globals = []GlobalSeg{{Name: "example.com/big.table", Base: 0x600000, Size: 20000, Section: ".data", Bytes: big[:20000]}}
	lean := string(renderLean(x))
	for _, want := range []string{"def seg0_words_0 : List Nat :=", "def seg0_words : List Nat :=", "words := seg0_words }",
		"def data0_bytes_0 : List Nat :=", "bytes := data0_bytes }", "def global0_init_0 : List Nat :=", "init := global0_init }"} {
		if !strings.Contains(lean, want) {
			t.Errorf("large arm64 program lacks %q", want)
		}
	}
	if strings.Contains(lean, "set_option maxRecDepth 100000 in\ndef seg0 :") || strings.Contains(lean, "set_option maxRecDepth 100000 in\ndef data0 :") {
		t.Errorf("tree-shaped records need no maxRecDepth")
	}
	if testing.Short() {
		return
	}
	if _, err := findLake(); err != nil {
		t.Skip("lake not installed")
	}
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "Extracted.lean"), []byte(lean), 0o644); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("lake", "env", "lean", filepath.Join(dir, "Extracted.lean"))
	cmd.Dir = repoRoot
	start := time.Now()
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("arm64 Extracted.lean does not elaborate: %v\n%.2000s", err, out)
	}
	t.Logf("arm64 40000 words + 30 KB data + 20 KB global: %v", time.Since(start))
}
