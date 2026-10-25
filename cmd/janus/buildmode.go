package main

// Instrumented build modes (docs/CLI.md, "Build modes").
//
// The Go toolchain has build modes that rewrite the compiled code. Janus detects them from the
// binary, before it extracts anything, and either rejects the binary or accepts it and records
// the mode in identity.json (`buildModes`):
//
//   - -race, -msan, -asan, -d=libfuzzer: rejected. The whole program's semantics rely on an
//     instrumented C runtime (ThreadSanitizer, MemorySanitizer, AddressSanitizer, libFuzzer)
//     that Janus does not model, so even an entry function that does not itself call the
//     instrumentation is refused.
//   - -cover: accepted ("cover"). Counter updates are ordinary stores of the covered function.
//   - -d=checkptr: accepted ("checkptr") when the extracted code calls runtime.checkptrAlignment
//     or runtime.checkptrArithmetic; they are ordinary code, or contracts named with --contract.
//   - -spectre=ret (amd64): accepted ("spectre=ret"). The retpoline thunks are runtime assembly
//     the extraction copies and executes.
//
// Detection reads the symbol table (ELF .symtab and .dynsym, or the functions of the pclntab),
// the section headers and the build settings of debug/buildinfo. It is a function of the
// binary's bytes, cached by SHA-256.

import (
	"bytes"
	"crypto/sha256"
	"debug/buildinfo"
	"debug/elf"
	"encoding/hex"
	"fmt"
	"os"
	"strings"
	"sync"
)

// buildSignals is what the build-mode decision looks at.
type buildSignals struct {
	names    map[string]bool   // every symbol name (functions, data, undefined imports)
	addrs    map[string]uint64 // addresses of defined symbols (first occurrence)
	sections map[string]bool   // ELF section names
	settings map[string]string // debug/buildinfo build settings (key -> value)
}

func (s *buildSignals) add(name string, addr uint64, defined bool) {
	if s.names == nil {
		s.names = map[string]bool{}
		s.addrs = map[string]uint64{}
	}
	s.names[name] = true
	if _, ok := s.addrs[name]; defined && !ok {
		s.addrs[name] = addr
	}
}

// has reports whether a symbol named name exists, with or without an `.abi0`/`.abiinternal`
// suffix.
func (s buildSignals) has(name string) bool {
	return s.names[name] || s.names[name+".abi0"] || s.names[name+".abiinternal"]
}

func (s buildSignals) hasPrefix(prefix string) bool {
	for n := range s.names {
		if strings.HasPrefix(n, prefix) {
			return true
		}
	}
	return false
}

// Build-mode values recorded in identity.json, in this order.
const (
	modeCover    = "cover"
	modeCheckptr = "checkptr"
	modeSpectre  = "spectre=ret"
)

const (
	msgRace = "built with -race: the race detector instruments every memory access with calls into the ThreadSanitizer runtime (runtime.raceread, ...); concurrency is out of scope for Janus (docs/SOUNDNESS.md). Rebuild without -race."
	msgMsan = "built with -msan: every load and store calls the MemorySanitizer C runtime (runtime.msanread -> __msan_read_go) through the cgo boundary, whose shadow memory, reports and aborts Janus does not model. A Janus proof already establishes that every access stays inside the memory the precondition grants, which is what the sanitizer checks dynamically: verify the binary built without -msan."
	msgAsan = "built with -asan: every load and store calls the AddressSanitizer C runtime (runtime.asanread -> __asan_read_go) through the cgo boundary, whose shadow memory, reports and aborts Janus does not model. A Janus proof already establishes that every access stays inside the memory the precondition grants, which is what the sanitizer checks dynamically: verify the binary built without -asan."
	msgFuzz = "built with -d=libfuzzer: comparisons call libFuzzer's C hooks (runtime.libfuzzerTraceCmp*, __sanitizer_cov_trace_cmp*) and the 8-bit coverage counters live in the libFuzzer section __sancov_cntrs; a libFuzzer build is a c-archive for libFuzzer's C driver, not a Go program Janus verifies. Verify the binary built without -d=libfuzzer."

	noteCover    = "note: built with -cover: coverage counter updates are ordinary stores into the package's counter variable; a theorem states them (Janus/Contracts/Instrument.lean, CovBlock)"
	noteCheckptr = "note: built with -d=checkptr: the code calls the runtime's pointer checks (runtime.checkptrAlignment, runtime.checkptrArithmetic), which are extracted as code unless --contract names them"
	noteSpectre  = "note: built with -spectre=ret: indirect calls go through the runtime's retpoline thunks, which are executed like any other code; their targets are dynamic call targets (--targets)"
)

// retpolineRegs are the registers of the amd64 runtime's retpoline thunks
// (runtime.retpolineAX .. runtime.retpolineR15).
var retpolineRegs = []string{"AX", "CX", "DX", "BX", "SP", "BP", "SI", "DI",
	"R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"}

func buildModeErr(flag, msg string) error {
	return &diag{
		Msg:   msg,
		Stage: "code extraction",
		Next:  fmt.Sprintf("Rebuild the program without %s (the same go build command without the flag) and extract from that binary.", flag),
	}
}

// classifyBuildModes is the decision table: an error for a rejected mode (race, msan, asan,
// libfuzzer, checked in that order), otherwise the accepted binary-wide modes ("cover",
// "spectre=ret"). "checkptr" depends on the extracted code (withCheckptr).
func classifyBuildModes(s buildSignals) ([]string, error) {
	set := func(k string) bool { return s.settings[k] == "true" }
	switch {
	case set("-race") || s.has("runtime.racefuncenter") || s.has("runtime.raceread") || s.names["__tsan_init"]:
		return nil, buildModeErr("-race", msgRace)
	case set("-msan") || s.has("runtime.msanread") || s.names["__msan_init"]:
		return nil, buildModeErr("-msan", msgMsan)
	case set("-asan") || s.has("runtime.asanread") || s.names["__asan_init"]:
		return nil, buildModeErr("-asan", msgAsan)
	case s.hasPrefix("runtime.libfuzzerTraceCmp") || s.hasPrefix("runtime.libfuzzerTraceConstCmp") ||
		s.has("runtime.libfuzzerHookStrCmp") || s.has("runtime.libfuzzerHookEqualFold") ||
		s.sections["__sancov_cntrs"] || s.names["runtime.__start___sancov_cntrs"] || s.names["__start___sancov_cntrs"]:
		return nil, buildModeErr("-d=libfuzzer", msgFuzz)
	}
	var modes []string
	// runtime.covctrs/ecovctrs are linked into every binary; the counters exist when they
	// delimit a non-empty range.
	lo, okLo := s.addrs["runtime.covctrs"]
	hi, okHi := s.addrs["runtime.ecovctrs"]
	if set("-cover") || s.has("runtime.addCovMeta") || (okLo && okHi && hi > lo) {
		modes = append(modes, modeCover)
	}
	for _, r := range retpolineRegs {
		if s.has("runtime.retpoline" + r) {
			modes = append(modes, modeSpectre)
			break
		}
	}
	return modes, nil
}

type buildModeResult struct {
	modes []string
	err   error
}

var buildModeCache sync.Map // binary SHA-256 -> buildModeResult

// detectBuildModes returns the accepted binary-wide build modes of b, or the error for a
// rejected one.
func detectBuildModes(b *Binary) ([]string, error) {
	// Callers may modify a returned *diag (check marks it Invalid), so each call gets a copy.
	fresh := func(r buildModeResult) ([]string, error) {
		if d, ok := r.err.(*diag); ok {
			c := *d
			return nil, &c
		}
		return append([]string(nil), r.modes...), r.err
	}
	if b.Sha256 != "" {
		if v, ok := buildModeCache.Load(b.Sha256); ok {
			return fresh(v.(buildModeResult))
		}
	}
	s, err := binarySignals(b)
	if err != nil {
		return nil, err
	}
	modes, err := classifyBuildModes(s)
	r := buildModeResult{modes, err}
	if b.Sha256 != "" {
		buildModeCache.Store(b.Sha256, r)
	}
	return fresh(r)
}

// binarySignals collects the symbols b was loaded with and, from the file (checked to be the
// bytes b was loaded from), the full ELF symbol tables, the section names and the build
// settings.
func binarySignals(b *Binary) (buildSignals, error) {
	var s buildSignals
	s.sections = map[string]bool{}
	s.settings = map[string]string{}
	for _, f := range b.Funcs {
		s.add(f.Name, f.Addr, true)
	}
	for _, f := range b.dataSyms {
		s.add(f.Name, f.Addr, true)
	}
	for _, f := range b.markers {
		s.add(f.Name, f.Addr, true)
	}
	for _, sec := range b.sections {
		s.sections[sec.Name] = true
	}
	if b.Path == "" {
		return s, nil
	}
	data, err := os.ReadFile(b.Path)
	if err != nil {
		return s, &diag{Msg: fmt.Sprintf("Cannot read binary %s: %v", b.Path, err), Stage: "binary identity",
			Next: "Pass the path of the Go executable."}
	}
	if sum := sha256.Sum256(data); b.Sha256 != "" && hex.EncodeToString(sum[:]) != b.Sha256 {
		return s, &diag{Msg: fmt.Sprintf("%s changed while Janus was reading it", b.Path), Stage: "binary identity",
			Next: "Extract again once the binary is no longer being written."}
	}
	if f, err := elf.NewFile(bytes.NewReader(data)); err == nil {
		for _, sec := range f.Sections {
			s.sections[sec.Name] = true
		}
		syms, _ := f.Symbols()
		dyn, _ := f.DynamicSymbols()
		for _, sym := range append(syms, dyn...) {
			if sym.Name == "" || elf.ST_TYPE(sym.Info) == elf.STT_SECTION || elf.ST_TYPE(sym.Info) == elf.STT_FILE {
				continue
			}
			s.add(sym.Name, sym.Value, sym.Section != elf.SHN_UNDEF)
		}
	}
	if bi, err := buildinfo.Read(bytes.NewReader(data)); err == nil {
		for _, kv := range bi.Settings {
			s.settings[kv.Key] = kv.Value
		}
	}
	return s, nil
}

// withCheckptr adds "checkptr" (in table order) when the extraction copies, or records as a
// contract or omitted call, one of the -d=checkptr runtime checks.
func withCheckptr(modes []string, x *Extraction) []string {
	is := func(n string) bool {
		n = strings.TrimSuffix(strings.TrimSuffix(n, ".abi0"), ".abiinternal")
		return n == "runtime.checkptrAlignment" || n == "runtime.checkptrArithmetic"
	}
	found := false
	for _, s := range x.Segments {
		found = found || is(s.Name)
	}
	for _, c := range x.Contracts {
		found = found || is(c.Name)
	}
	for _, o := range x.Omitted {
		found = found || is(o.Name)
	}
	if !found {
		return modes
	}
	out := []string{}
	for _, m := range modes {
		if m == modeCover {
			out = append(out, m)
		}
	}
	out = append(out, modeCheckptr)
	for _, m := range modes {
		if m != modeCover {
			out = append(out, m)
		}
	}
	return out
}

// buildModeNotes are the informational lines `janus extract` prints for the accepted modes.
func buildModeNotes(modes []string) []string {
	var notes []string
	for _, m := range modes {
		switch m {
		case modeCover:
			notes = append(notes, noteCover)
		case modeCheckptr:
			notes = append(notes, noteCheckptr)
		case modeSpectre:
			notes = append(notes, noteSpectre)
		}
	}
	return notes
}
