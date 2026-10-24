package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"regexp"
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

// Contract is a function named by --contract: direct calls to it are not followed, and its
// address is recorded in Program.contracts. Its behaviour is whatever the theorem's contract
// hypotheses (a `Summary` of the program linked with arbitrary code) say; without one, control
// reaching it faults with noCode, exactly as for any other address without extracted code.
type Contract struct {
	Name string
	Addr uint64
}

type Extraction struct {
	Bin       *Binary
	Entry     Func
	Contracts []Contract // discovery order
	// ContractPatterns are the --contract patterns, as given (recorded in identity.json so
	// that check regenerates the same extraction).
	ContractPatterns []string
	Segments         []Segment // entry first, then breadth-first discovery order
	Stubs            []Stub    // discovery order
	Unresolved       []Unresolved
	// Dynamic targets: --targets as given, and every function added because an indirect call
	// may reach it (see dynamic.go). Omitted: direct calls deliberately not followed.
	Targets  []string
	Dynamic  []DynTarget
	Omitted  []OmittedCall
	Data     []DataSeg     // read-only objects the code references, sorted by address
	DataRefs []DataRef     // detected references, in code order
	Skipped  []SkippedData // references whose target is not copied (writable, code, ...)
	Lean     []byte
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
func extract(binPath, sym string, maxFunctions int, contracts ...string) (*Extraction, error) {
	b, err := loadBinary(binPath)
	if err != nil {
		return nil, err
	}
	return extractWith(b, sym, maxFunctions, contracts)
}

func extractFrom(b *Binary, sym string, maxFunctions int) (*Extraction, error) {
	return extractWith(b, sym, maxFunctions, nil)
}

// contractMatcher matches function names against --contract glob patterns: `*` matches any
// run of characters (including `.` and `/`), `?` any one character, everything else itself.
// A name matches with or without its `.abi0`/`.abiinternal` suffix.
type contractMatcher struct {
	pats []string
	res  []*regexp.Regexp
}

func newContractMatcher(pats []string) (*contractMatcher, error) {
	m := &contractMatcher{pats: pats}
	for _, p := range pats {
		if p == "" {
			return nil, usageErr("--contract needs a non-empty symbol or glob pattern")
		}
		var sb strings.Builder
		sb.WriteString("^")
		for _, r := range p {
			switch r {
			case '*':
				sb.WriteString(".*")
			case '?':
				sb.WriteString(".")
			default:
				sb.WriteString(regexp.QuoteMeta(string(r)))
			}
		}
		sb.WriteString("$")
		m.res = append(m.res, regexp.MustCompile(sb.String()))
	}
	return m, nil
}

func (m *contractMatcher) match(name string) bool {
	if m == nil {
		return false
	}
	n := strings.TrimSuffix(strings.TrimSuffix(name, ".abi0"), ".abiinternal")
	for _, re := range m.res {
		if re.MatchString(name) || re.MatchString(n) {
			return true
		}
	}
	return false
}

// contractTarget records g as a contract (once) if it matches; true if the branch to it must
// not be followed. Stubs keep their stub meaning (checked by the caller first).
func (x *Extraction) contractTarget(m *contractMatcher, seen map[uint64]bool, g Func) bool {
	if !m.match(g.Name) {
		return false
	}
	if !seen[g.Addr] {
		seen[g.Addr] = true
		x.Contracts = append(x.Contracts, Contract{Name: g.Name, Addr: g.Addr})
	}
	return true
}

// extractArm64Func copies one arm64 function and lists its direct branches.
func extractArm64Func(b *Binary, f Func) (Segment, []Unresolved, error) {
	ws, err := b.words(f)
	if err != nil {
		return Segment{}, nil, err
	}
	var brs []Unresolved
	for i, w := range ws {
		pc := f.Addr + 4*uint64(i)
		if t, ok := branchTarget(w, pc); ok {
			brs = append(brs, Unresolved{From: pc, Target: t})
		}
	}
	return Segment{Name: f.Name, Base: f.Addr, Size: f.Size, Words: ws}, brs, nil
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
	writeProgram(&sb, x, "Program")
	fmt.Fprintf(&sb, "def entry : Nat := 0x%x\n\n", x.Entry.Addr)
	sb.WriteString("end Extracted\n")
	return []byte(sb.String())
}

// writeContracts renders `def contracts` (only when there are contracts, so extractions
// without --contract are byte-identical to earlier ones).
func writeContracts(sb *strings.Builder, cs []Contract) {
	sb.WriteString("def contracts : List (String × Nat) := [")
	for i, c := range cs {
		if i > 0 {
			sb.WriteString(",")
		}
		fmt.Fprintf(sb, "\n  (%s, 0x%x)", leanString(c.Name), c.Addr)
	}
	sb.WriteString(" ]\n\n")
}

// writeProgram renders the data and contract lists (if any) and `def program`.
func writeProgram(sb *strings.Builder, x *Extraction, ty string) {
	fields := "segments := segments, stubs := stubs, exitAddr := exitAddr"
	if len(x.Data) > 0 {
		writeData(sb, x.Data)
		fields += ", data := data"
	}
	if len(x.Contracts) > 0 {
		writeContracts(sb, x.Contracts)
		fields += ", contracts := contracts"
	}
	if len(x.Data) == 0 && len(x.Contracts) == 0 {
		fmt.Fprintf(sb, "def program : %s := { %s }\n\n", ty, fields)
		return
	}
	fmt.Fprintf(sb, "def program : %s :=\n  { %s }\n\n", ty, fields)
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
