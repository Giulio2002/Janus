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

// Round 7 G1: the runtime functions Janus treats as stubs, by their exact linked (ELF .symtab)
// names. A name alone does not identify package runtime: any package may define a Go-assembly
// TEXT symbol `runtime·panicX` or push one with `//go:linkname f runtime.panicX` (neither needs
// -checklinkname=0), and round 6 classified every `runtime.panic*`/`runtime.morestack*` name
// without '/' as a stub, so an ordinary function that returns (or panics) was taken for a panic
// (or morestack) stub. The lists below are exactly the functions of that kind that the go1.26
// runtime defines for linux/arm64 and linux/amd64 (`go tool nm` on the runtime archive of
// go1.26.0 and go1.26.10, both architectures; minus panicCheck1/2, which return, and
// morestackc, a fatal throw that only runtime code calls). Because the runtime itself defines
// each of them, another definition with the same name and ABI is a link error ("duplicated
// definition of symbol"), and one with the other ABI is linked under a mangled name
// (`runtime.panicdivide.abi0`), which is not on the list. That argument needs the go1.26
// runtime, the ELF symbol table (the pclntab does not record the ABI, so names there are not
// mangled), and a name that occurs once (`//go:linkname f runtime.morestack_noctxt.abi0`
// gives a second symbol with exactly that name). `classifyStub` checks all three.
var (
	runtimePanicStubs = map[string]bool{
		"runtime.gopanic": true, "runtime.goPanicIndex": true, "runtime.goPanicIndexU": true,
		"runtime.goPanicSlice3Acap": true, "runtime.goPanicSlice3AcapU": true,
		"runtime.goPanicSlice3Alen": true, "runtime.goPanicSlice3AlenU": true,
		"runtime.goPanicSlice3B": true, "runtime.goPanicSlice3BU": true,
		"runtime.goPanicSlice3C": true, "runtime.goPanicSlice3CU": true,
		"runtime.goPanicSliceAcap": true, "runtime.goPanicSliceAcapU": true,
		"runtime.goPanicSliceAlen": true, "runtime.goPanicSliceAlenU": true,
		"runtime.goPanicSliceB": true, "runtime.goPanicSliceBU": true,
		"runtime.goPanicSliceConvert": true,
		"runtime.panicBounds":         true, "runtime.panicBounds32": true, "runtime.panicBounds32X": true,
		"runtime.panicBounds64": true, "runtime.panicdivide": true, "runtime.panicdottypeE": true,
		"runtime.panicdottypeI": true, "runtime.panicfloat": true, "runtime.panicmakeslicecap": true,
		"runtime.panicmakeslicelen": true, "runtime.panicmem": true, "runtime.panicmemAddr": true,
		"runtime.panicnildottype": true, "runtime.panicoverflow": true,
		"runtime.panicrangestate": true, "runtime.panicshift": true, "runtime.panicSimdImm": true,
		"runtime.panicunsafeslicelen": true, "runtime.panicunsafeslicelen1": true,
		"runtime.panicunsafeslicenilptr": true, "runtime.panicunsafeslicenilptr1": true,
		"runtime.panicunsafestringlen": true, "runtime.panicunsafestringnilptr": true,
		"runtime.panicwrap": true,
	}
	// morestack and morestack_noctxt are ABI0 assembly; the linker names them with ".abi0".
	runtimeMorestackStubs = map[string]bool{
		"runtime.morestack.abi0": true, "runtime.morestack_noctxt.abi0": true,
	}
)

// stubGoVersion is the Go release whose runtime the stub lists are taken from.
const stubGoVersion = "go1.26"

// stubKind classifies a linked symbol name as a runtime stub (name only; see classifyStub for
// the checks that make the name trustworthy).
func stubKind(name string) (StubKind, bool) {
	switch {
	case runtimeMorestackStubs[name]:
		return stubMorestack, true
	case runtimePanicStubs[name]:
		return stubPanic, true
	}
	return "", false
}

// stubLike reports whether name looks like a runtime stub under any ABI suffix (used only to
// give a useful diagnostic when classifyStub cannot authenticate one).
func stubLike(name string) bool {
	n := strings.TrimSuffix(name, ".abi0")
	_, ok1 := stubKind(n)
	_, ok2 := stubKind(n + ".abi0")
	return ok1 || ok2
}

// classifyStub decides whether the function g, the target of a direct branch, is a runtime
// stub. It is one only if its name is on the go1.26 lists, the binary was linked with a go1.26
// runtime, its names come from the ELF symbol table, and no other function has the same name
// (round 7 G1). A listed name that fails one of the other checks is an error: extracting the
// runtime function as code would give a different, much larger program.
func (b *Binary) classifyStub(g Func) (StubKind, bool, error) {
	k, ok := stubKind(g.Name)
	if !ok {
		if b.SymbolSource != "symtab" && stubLike(g.Name) {
			return "", false, &diag{
				Msg:   fmt.Sprintf("the code calls %s, but %s has no ELF symbol table, and function names from the pclntab do not record the ABI, so Janus cannot tell the runtime's %s from a function of another package that only has that name (round 7 G1)", g.Name, b.Path, g.Name),
				Stage: "code extraction",
				Next:  "Rebuild without stripping the symbol table (no -ldflags=-s).",
			}
		}
		return "", false, nil
	}
	if b.SymbolSource != "symtab" {
		return "", false, &diag{
			Msg:   fmt.Sprintf("the code calls %s, but %s has no ELF symbol table, so Janus cannot confirm it is the runtime's (round 7 G1)", g.Name, b.Path),
			Stage: "code extraction",
			Next:  "Rebuild without stripping the symbol table (no -ldflags=-s).",
		}
	}
	if b.GoVersion != stubGoVersion && !strings.HasPrefix(b.GoVersion, stubGoVersion+".") &&
		!strings.HasPrefix(b.GoVersion, stubGoVersion+"rc") {
		return "", false, &diag{
			Msg:   fmt.Sprintf("the code calls %s, but %s was built with %s, and Janus's list of runtime stubs (which runtime functions panic, which grow the stack) is taken from the %s runtime (round 7 G1)", g.Name, b.Path, b.GoVersion, stubGoVersion),
			Stage: "code extraction",
			Next:  "Build the binary with a " + stubGoVersion + " toolchain (GOTOOLCHAIN=go1.26.0).",
		}
	}
	n := 0
	for _, f := range b.Funcs {
		if f.Name == g.Name {
			n++
		}
	}
	if n != 1 {
		return "", false, &diag{
			Msg:   fmt.Sprintf("the code calls %s, but %s defines %d functions with that name, so the runtime's cannot be told from the others (round 7 G1: //go:linkname can push a second symbol with a runtime stub's name)", g.Name, b.Path, n),
			Stage: "code extraction",
			Next:  "Remove the //go:linkname or assembly definition that reuses a runtime function's name.",
		}
	}
	return k, true, nil
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
	if stubLike(entry.Name) {
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
			k, ok, err := b.classifyStub(g)
			if err != nil {
				return nil, err
			}
			if ok {
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
