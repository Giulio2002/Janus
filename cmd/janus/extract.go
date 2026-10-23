package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"strings"
)

const extractorVersion = "0.2.0"

const defaultMaxFunctions = 64

// Segment is one copied function.
type Segment struct {
	Name  string
	Base  uint64
	Size  uint64 // symbol size, including padding
	Words []uint32
	Bytes []byte // amd64: the raw bytes of [Base, Base+Size) (Words is empty)
}

// StubKind mirrors Janus.StubKind.
type StubKind string

const (
	stubPanic     StubKind = "panic"
	stubMorestack StubKind = "morestack"
)

type Stub struct {
	Name string
	Addr uint64
	Kind StubKind
}

// Unresolved is a direct branch whose target is in no known function; it is not copied.
type Unresolved struct {
	From   uint64
	Target uint64
}

type Extraction struct {
	Bin        *Binary
	Entry      Func
	Segments   []Segment // entry first, then breadth-first discovery order
	Stubs      []Stub    // discovery order
	Unresolved []Unresolved
	Data       []DataSeg     // read-only objects the code references, sorted by address
	DataRefs   []DataRef     // detected references, in code order
	Skipped    []SkippedData // references whose target is not copied (writable, code, ...)
	Lean       []byte
}

// stubKind classifies runtime functions that end execution with a named outcome.
func stubKind(name string) (StubKind, bool) {
	n := strings.TrimSuffix(strings.TrimSuffix(name, ".abi0"), ".abiinternal")
	switch {
	case strings.HasPrefix(n, "runtime.morestack"):
		return stubMorestack, true
	case strings.HasPrefix(n, "runtime.panic"), strings.HasPrefix(n, "runtime.goPanic"), n == "runtime.gopanic":
		return stubPanic, true
	}
	return "", false
}

// extract copies sym and every function reachable from it by direct branches.
func extract(binPath, sym string, maxFunctions int) (*Extraction, error) {
	b, err := loadBinary(binPath)
	if err != nil {
		return nil, err
	}
	return extractFrom(b, sym, maxFunctions)
}

func extractFrom(b *Binary, sym string, maxFunctions int) (*Extraction, error) {
	entry, err := b.lookup(sym)
	if err != nil {
		return nil, err
	}
	if _, ok := stubKind(entry.Name); ok {
		return nil, &diag{Msg: fmt.Sprintf("%s is a runtime stub, not a function Janus extracts", entry.Name),
			Stage: "function selection", Next: "Select a Go function that calls the stub instead."}
	}
	if b.GOARCH == "amd64" {
		return extractAmd64(b, entry, maxFunctions)
	}
	x := &Extraction{Bin: b, Entry: entry}
	seen := map[uint64]bool{entry.Addr: true}
	stubSeen := map[uint64]bool{}
	queue := []Func{entry}
	for len(queue) > 0 {
		f := queue[0]
		queue = queue[1:]
		ws, err := b.words(f)
		if err != nil {
			return nil, &diag{Msg: err.Error(), Stage: "code extraction", Next: "Report this binary layout to the Janus maintainers."}
		}
		x.Segments = append(x.Segments, Segment{Name: f.Name, Base: f.Addr, Size: f.Size, Words: ws})
		for i, w := range ws {
			pc := f.Addr + 4*uint64(i)
			t, ok := branchTarget(w, pc)
			if !ok || (t >= f.Addr && t < f.End()) {
				continue
			}
			g, ok := b.containing(t)
			if !ok {
				x.Unresolved = append(x.Unresolved, Unresolved{From: pc, Target: t})
				continue
			}
			if k, ok := stubKind(g.Name); ok {
				if !stubSeen[g.Addr] {
					stubSeen[g.Addr] = true
					x.Stubs = append(x.Stubs, Stub{Name: g.Name, Addr: g.Addr, Kind: k})
				}
				continue
			}
			if !seen[g.Addr] {
				seen[g.Addr] = true
				queue = append(queue, g)
			}
		}
		if len(x.Segments)+len(queue) > maxFunctions {
			var names []string
			for _, s := range x.Segments {
				names = append(names, s.Name)
			}
			for _, q := range queue {
				names = append(names, q.Name)
			}
			if len(names) > 20 {
				names = append(names[:20], fmt.Sprintf("... and %d more", len(names)-20))
			}
			return nil, &diag{
				Msg: fmt.Sprintf("%s reaches more than %d functions by direct branches:\n    %s",
					entry.Name, maxFunctions, strings.Join(names, "\n    ")),
				Stage: "code extraction",
				Next:  "Raise the limit with --max-functions N if this is intended, or extract a smaller function.",
			}
		}
	}
	for _, s := range x.Segments {
		x.DataRefs = append(x.DataRefs, dataRefs(s.Words, s.Base)...)
	}
	x.Data, x.Skipped = collectData(b, x.DataRefs)
	x.Lean = renderLean(x)
	return x, nil
}

func leanString(s string) string {
	var sb strings.Builder
	sb.WriteByte('"')
	for _, r := range s {
		switch {
		case r == '"' || r == '\\':
			sb.WriteByte('\\')
			sb.WriteRune(r)
		case r < 0x20 || r == 0x7f:
			fmt.Fprintf(&sb, "\\x%02x", r)
		default:
			sb.WriteRune(r)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

const wordsPerLine = 8

// Lean elaborates one large list literal with deep recursion: around 3000 words in a single
// definition exceed the default maxRecDepth. Programs up to inlineWordLimit words are written
// with all segments inline in `segments`; larger ones get one definition per segment.
const (
	inlineWordLimit  = 2048
	segmentWordLimit = 1024 // above this, a segment definition raises maxRecDepth
)

const bytesPerLine = 16

func writeDataSegment(sb *strings.Builder, d DataSeg, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, bytes := [", leanString(d.Name), d.Base)
	multi := len(d.Bytes) > bytesPerLine
	for j, v := range d.Bytes {
		if j > 0 {
			sb.WriteString(",")
			if !(multi && j%bytesPerLine == 0) {
				sb.WriteString(" ")
			}
		}
		if multi && j%bytesPerLine == 0 {
			sb.WriteString("\n" + indent + "    ")
		}
		fmt.Fprintf(sb, "0x%02x", v)
	}
	sb.WriteString("] }")
}

func writeSegment(sb *strings.Builder, s Segment, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, words := [", leanString(s.Name), s.Base)
	multi := len(s.Words) > wordsPerLine
	for j, w := range s.Words {
		if j > 0 {
			sb.WriteString(",")
			if !(multi && j%wordsPerLine == 0) {
				sb.WriteString(" ")
			}
		}
		if multi && j%wordsPerLine == 0 {
			sb.WriteString("\n" + indent + "    ")
		}
		fmt.Fprintf(sb, "0x%08x", w)
	}
	sb.WriteString("] }")
}

// renderLean produces Extracted.lean. The output is a pure function of the extraction, so
// `janus check` can compare it byte for byte.
func renderLean(x *Extraction) []byte {
	var sb strings.Builder
	sb.WriteString("import Janus\n\n")
	fmt.Fprintf(&sb, "/-! Generated by `janus extract` %s from `%s` (%s, %s).\n", extractorVersion, x.Entry.Name, x.Bin.MainModule, x.Bin.GoVersion)
	sb.WriteString("Do not edit: `janus check` regenerates this file from the binary and compares it byte for byte.\n")
	sb.WriteString("The binary's SHA-256 is recorded in `identity.json`. -/\n\n")
	sb.WriteString("namespace Extracted\nopen Janus\n\n")
	total := 0
	for _, s := range x.Segments {
		total += len(s.Words)
	}
	if total <= inlineWordLimit {
		sb.WriteString("def segments : List Segment := [")
		for i, s := range x.Segments {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeSegment(&sb, s, "  ")
		}
		sb.WriteString(" ]\n\n")
	} else {
		for i, s := range x.Segments {
			if len(s.Words) > segmentWordLimit {
				sb.WriteString("set_option maxRecDepth 100000 in\n")
			}
			fmt.Fprintf(&sb, "def seg%d : Segment :=\n  ", i)
			writeSegment(&sb, s, "  ")
			sb.WriteString("\n\n")
		}
		sb.WriteString("def segments : List Segment := [")
		for i := range x.Segments {
			if i > 0 {
				sb.WriteString(",")
				if i%wordsPerLine != 0 {
					sb.WriteString(" ")
				}
			}
			if i%wordsPerLine == 0 {
				sb.WriteString("\n  ")
			}
			fmt.Fprintf(&sb, "seg%d", i)
		}
		sb.WriteString(" ]\n\n")
	}
	sb.WriteString("def stubs : List Stub := [")
	for i, st := range x.Stubs {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(&sb, "\n  { name := %s, addr := 0x%x, kind := .%s }", leanString(st.Name), st.Addr, st.Kind)
	}
	if len(x.Stubs) > 0 {
		sb.WriteString(" ")
	}
	sb.WriteString("]\n\n")
	sb.WriteString("def exitAddr : Nat := 0\n\n")
	if len(x.Data) == 0 {
		sb.WriteString("def program : Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }\n\n")
	} else {
		writeData(&sb, x.Data)
		sb.WriteString("def program : Program :=\n  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }\n\n")
	}
	fmt.Fprintf(&sb, "def entry : Nat := 0x%x\n\n", x.Entry.Addr)
	sb.WriteString("end Extracted\n")
	return []byte(sb.String())
}

// writeData renders `def data`, inline when small, else one definition per object (like
// large code segments).
func writeData(sb *strings.Builder, data []DataSeg) {
	total := 0
	for _, d := range data {
		total += len(d.Bytes)
	}
	if total <= inlineWordLimit {
		sb.WriteString("def data : List DataSegment := [")
		for i, d := range data {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeDataSegment(sb, d, "  ")
		}
		sb.WriteString(" ]\n\n")
		return
	}
	for i, d := range data {
		if len(d.Bytes) > segmentWordLimit {
			sb.WriteString("set_option maxRecDepth 100000 in\n")
		}
		fmt.Fprintf(sb, "def data%d : DataSegment :=\n  ", i)
		writeDataSegment(sb, d, "  ")
		sb.WriteString("\n\n")
	}
	sb.WriteString("def data : List DataSegment := [")
	for i := range data {
		if i > 0 {
			sb.WriteString(",")
			if i%wordsPerLine != 0 {
				sb.WriteString(" ")
			}
		}
		if i%wordsPerLine == 0 {
			sb.WriteString("\n  ")
		}
		fmt.Fprintf(sb, "data%d", i)
	}
	sb.WriteString(" ]\n\n")
}

func sha256Hex(b []byte) string {
	s := sha256.Sum256(b)
	return hex.EncodeToString(s[:])
}
