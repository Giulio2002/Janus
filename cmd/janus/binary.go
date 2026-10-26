package main

import (
	"bytes"
	"crypto/sha256"
	"debug/buildinfo"
	"debug/elf"
	"debug/gosym"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"os"
	"sort"
	"strings"
	"sync"
)

// Func is one function of the binary's text, from the ELF symbol table or the pclntab.
type Func struct {
	Name string
	Addr uint64
	Size uint64
}

func (f Func) End() uint64 { return f.Addr + f.Size }

// Binary is a validated linux/arm64 Go ELF executable.
type Binary struct {
	Path       string
	Sha256     string
	GoVersion  string
	MainModule string
	GOOS       string
	GOARCH     string
	GOAMD64    string // amd64 only: the GOAMD64 build setting, if recorded
	// SymbolSource is "symtab" or "pclntab".
	SymbolSource string
	Funcs        []Func // sorted by address

	text     []byte
	textAddr uint64
	// goText is the address of runtime.text, the base of the pclntab's function offsets: the
	// start of .text, except in an externally linked (cgo) binary, where C code comes first.
	goText uint64

	sections []section // allocated sections (in memory at run time), sorted by address
	loads    []loadSeg // the PT_LOAD program headers (globals.go: where .bss is zero-filled)
	dataSyms []Func    // non-function symbols with a size (data objects), sorted by address
	markers  []Func    // zero-size object symbols (go:string.*, runtime.rodata, ...), sorted by address

	stubMu    sync.Mutex
	stubCache map[uint64]stubVerdict // classifyStub results by function address
	pcln      *gosym.Table           // parsed .gopclntab (stub pins), nil until needed
	pclnErr   error

	cenv *cenvInfo // the C environment: PLT, GOT, TLS (cenv.go)
}

// section is an allocated ELF section. data is nil for SHT_NOBITS (.bss, .noptrbss).
type section struct {
	Name     string
	Addr     uint64
	Size     uint64
	Writable bool
	Exec     bool
	NoBits   bool
	data     []byte
}

func (s section) End() uint64 { return s.Addr + s.Size }

// validateSegments checks that every file-backed allocated section (the bytes the extractor
// copies: .text, .rodata, literal pools, .gopclntab, ...) is backed by a PT_LOAD segment that
// maps it with a consistent file-offset -> virtual-address delta, and that the segment holding
// `.text` is executable. The kernel loads only through PT_LOAD, so this makes the bytes Janus
// reads at a virtual address equal to the bytes that execute there. A mismatch (a lying section
// header, which a normal `go build` never produces) is rejected. See docs/AUDIT-MODEL.md EX1.
func validateSegments(f *elf.File, path string) error {
	// covers reports whether PT_LOAD p maps the [addr, addr+size) / [off, off+size) range of a
	// section with a single consistent delta (off - p.Off == addr - p.Vaddr), inside the file
	// image of the segment (Filesz, not Memsz: we only read file bytes).
	covers := func(p *elf.Prog, addr, off, size uint64) bool {
		if p.Type != elf.PT_LOAD {
			return false
		}
		if off < p.Off || off+size > p.Off+p.Filesz {
			return false
		}
		if addr < p.Vaddr || addr+size > p.Vaddr+p.Filesz {
			return false
		}
		return off-p.Off == addr-p.Vaddr
	}
	for _, s := range f.Sections {
		// Only sections with file bytes the extractor can read: allocated, not NOBITS (.bss),
		// nonzero. NOBITS sections carry no file content and are never copied.
		if s.Flags&elf.SHF_ALLOC == 0 || s.Type == elf.SHT_NOBITS || s.Size == 0 {
			continue
		}
		var seg *elf.Prog
		for _, p := range f.Progs {
			if covers(p, s.Addr, s.Offset, s.Size) {
				seg = p
				break
			}
		}
		if seg == nil {
			return &diag{
				Msg: fmt.Sprintf("section %s of %s (vaddr 0x%x, file offset 0x%x, size 0x%x) is not covered by a PT_LOAD segment with a matching file-to-address mapping; the bytes the kernel maps at that address would differ from the section's bytes, so Janus would reason about code or data that does not execute",
					s.Name, path, s.Addr, s.Offset, s.Size),
				Stage: "binary validation",
				Next:  "Use an unmodified executable produced by go build (the section and segment headers must agree).",
			}
		}
		if s.Name == ".text" && seg.Flags&elf.PF_X == 0 {
			return &diag{
				Msg:   fmt.Sprintf(".text of %s is mapped by a non-executable PT_LOAD segment; it is not the executed code", path),
				Stage: "binary validation",
				Next:  "Use an unmodified executable produced by go build.",
			}
		}
	}
	return nil
}

// loadBinary reads and validates path. Failures are diagnostics (*diag).
func loadBinary(path string) (*Binary, error) { return loadBinaryMode(path, false) }

// loadBinaryMode is loadBinary; allowPIE accepts ET_DYN. Only `janus stubpins` (which measures
// the runtime stubs' code and never extracts) passes true.
func loadBinaryMode(path string, allowPIE bool) (*Binary, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, &diag{
			Msg:   fmt.Sprintf("Cannot read binary %s: %v", path, err),
			Stage: "binary identity",
			Next:  "Pass the path of the Go executable (build it with scripts/build-examples.sh for the examples).",
		}
	}
	sum := sha256.Sum256(data)
	b := &Binary{Path: path, Sha256: hex.EncodeToString(sum[:])}

	f, err := elf.NewFile(bytes.NewReader(data))
	if err != nil {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s is not an ELF file: %v", path, err),
			Stage: "binary validation",
			Next:  "Build the Go program with GOOS=linux GOARCH=arm64.",
		}
	}
	if f.Class != elf.ELFCLASS64 || (f.Machine != elf.EM_AARCH64 && f.Machine != elf.EM_X86_64) || f.ByteOrder != binary.LittleEndian {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s is a %s %s %s ELF, not a 64-bit little-endian AArch64 or x86-64 one", path, f.Class, f.Data, f.Machine),
			Stage: "binary validation",
			Next:  "Build the Go program with GOOS=linux GOARCH=arm64.",
		}
	}
	// Reject PIE (ET_DYN). The extracted program records link-time virtual addresses, while a
	// position-independent executable is loaded at base+vaddr chosen at runtime, so the model's
	// addresses would not be the ones the code runs at. Only ET_EXEC is sound. (F6 in docs/AUDIT.md.)
	if f.Type == elf.ET_DYN && !allowPIE {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s is a position-independent executable (ET_DYN); Janus supports only non-PIE executables (ET_EXEC).", path),
			Stage: "binary validation",
			Next:  "Rebuild without PIE: go build -buildmode=exe (or set CGO_ENABLED=0), so the binary uses link-time addresses.",
		}
	}
	if f.Type != elf.ET_EXEC && !(allowPIE && f.Type == elf.ET_DYN) {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s is an ELF of type %s, not an executable (ET_EXEC).", path, f.Type),
			Stage: "binary validation",
			Next:  "Extract from a linked Go executable built with go build.",
		}
	}
	bi, err := buildinfo.Read(bytes.NewReader(data))
	if err != nil {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s has no Go build information: %v", path, err),
			Stage: "binary validation",
			Next:  "Janus extracts from executables built by the Go toolchain (go build).",
		}
	}
	b.GoVersion = bi.GoVersion
	b.MainModule = bi.Main.Path
	for _, s := range bi.Settings {
		switch s.Key {
		case "GOOS":
			b.GOOS = s.Value
		case "GOARCH":
			b.GOARCH = s.Value
		case "GOAMD64":
			b.GOAMD64 = s.Value
		}
	}
	if b.GOOS != "linux" || (b.GOARCH != "arm64" && b.GOARCH != "amd64") || (b.GOARCH == "amd64") != (f.Machine == elf.EM_X86_64) {
		return nil, &diag{
			Msg:   fmt.Sprintf("%s was built for GOOS=%s GOARCH=%s, not linux/arm64 or linux/amd64", path, b.GOOS, b.GOARCH),
			Stage: "binary validation",
			Next:  "Rebuild with GOOS=linux GOARCH=arm64 (or GOARCH=amd64).",
		}
	}

	text := f.Section(".text")
	if text == nil || text.Type != elf.SHT_PROGBITS {
		return nil, &diag{Msg: path + " has no .text section", Stage: "binary validation",
			Next: "Use an unmodified executable produced by go build."}
	}
	// The extractor copies code and read-only data by *section header* (vaddr + file offset),
	// but the kernel maps the image by *program header* (PT_LOAD). Those are two independent
	// descriptions of the file, and the loader ignores section headers entirely. If they
	// disagree — a corrupted or hand-edited `.text`/`.rodata` section header, or an unusual
	// linker layout — the bytes Janus reads at a vaddr are not the bytes that execute there,
	// so a theorem would be about different bytes than run. `janus check` would not catch it
	// (it re-reads the same section headers). Validate that every file-backed allocated section
	// is covered by a PT_LOAD whose file->vaddr mapping matches the section, with `.text`
	// executable, so the byte at any vaddr Janus reads equals the byte the kernel maps there.
	// (rt-model, docs/AUDIT-MODEL.md EX1.)
	if err := validateSegments(f, path); err != nil {
		return nil, err
	}
	if b.text, err = text.Data(); err != nil {
		return nil, &diag{Msg: fmt.Sprintf("cannot read .text of %s: %v", path, err), Stage: "binary validation",
			Next: "Use an unmodified executable produced by go build."}
	}
	b.textAddr = text.Addr
	b.goText = text.Addr
	for _, p := range f.Progs {
		if p.Type == elf.PT_LOAD {
			b.loads = append(b.loads, loadSeg{Vaddr: p.Vaddr, Filesz: p.Filesz, Memsz: p.Memsz, Writable: p.Flags&elf.PF_W != 0})
		}
	}

	for _, s := range f.Sections {
		if s.Flags&elf.SHF_ALLOC == 0 || s.Size == 0 {
			continue
		}
		sec := section{Name: s.Name, Addr: s.Addr, Size: s.Size, Writable: s.Flags&elf.SHF_WRITE != 0,
			Exec: s.Flags&elf.SHF_EXECINSTR != 0, NoBits: s.Type == elf.SHT_NOBITS}
		if !sec.NoBits {
			if sec.data, err = s.Data(); err != nil || uint64(len(sec.data)) != s.Size {
				return nil, &diag{Msg: fmt.Sprintf("cannot read section %s of %s: %v", s.Name, path, err), Stage: "binary validation",
					Next: "Use an unmodified executable produced by go build."}
			}
		}
		b.sections = append(b.sections, sec)
	}
	sort.SliceStable(b.sections, func(i, j int) bool { return b.sections[i].Addr < b.sections[j].Addr })

	if syms, err := f.Symbols(); err == nil && len(syms) > 0 {
		b.SymbolSource = "symtab"
		textIdx := -1
		for i, s := range f.Sections {
			if s == text {
				textIdx = i
			}
		}
		for _, s := range syms {
			if s.Name == "runtime.text" && s.Section != elf.SHN_UNDEF {
				b.goText = s.Value
			}
			if t := elf.ST_TYPE(s.Info); (t == elf.STT_OBJECT || t == elf.STT_NOTYPE) && s.Size > 0 &&
				s.Section != elf.SHN_UNDEF && s.Section < elf.SHN_LORESERVE {
				b.dataSyms = append(b.dataSyms, Func{Name: s.Name, Addr: s.Value, Size: s.Size})
			}
			if elf.ST_TYPE(s.Info) == elf.STT_OBJECT && s.Size == 0 && s.Section != elf.SHN_UNDEF && s.Section < elf.SHN_LORESERVE {
				b.markers = append(b.markers, Func{Name: s.Name, Addr: s.Value})
			}
			if elf.ST_TYPE(s.Info) != elf.STT_FUNC || int(s.Section) != textIdx {
				continue
			}
			b.Funcs = append(b.Funcs, Func{Name: s.Name, Addr: s.Value, Size: s.Size})
		}
	} else if pcln := f.Section(".gopclntab"); pcln != nil {
		b.SymbolSource = "pclntab"
		pdata, err := pcln.Data()
		if err == nil {
			var tab *gosym.Table
			tab, err = gosym.NewTable(nil, gosym.NewLineTable(pdata, text.Addr))
			if err == nil {
				for _, fn := range tab.Funcs {
					b.Funcs = append(b.Funcs, Func{Name: fn.Name, Addr: fn.Entry, Size: fn.End - fn.Entry})
				}
			}
		}
		if err != nil {
			return nil, &diag{Msg: fmt.Sprintf("cannot read .gopclntab of %s: %v", path, err), Stage: "binary validation",
				Next: "Build without stripping the symbol table (no -ldflags=-s)."}
		}
	} else {
		return nil, &diag{Msg: path + " has neither a .symtab nor a .gopclntab", Stage: "binary validation",
			Next: "Build without stripping the symbol table (no -ldflags=-s)."}
	}
	sort.SliceStable(b.Funcs, func(i, j int) bool { return b.Funcs[i].Addr < b.Funcs[j].Addr })
	sort.SliceStable(b.dataSyms, func(i, j int) bool { return b.dataSyms[i].Addr < b.dataSyms[j].Addr })
	sort.SliceStable(b.markers, func(i, j int) bool { return b.markers[i].Addr < b.markers[j].Addr })
	// Symbols without a size (some assembly functions) extend to the next symbol.
	for i := range b.Funcs {
		if b.Funcs[i].Size == 0 {
			end := b.textAddr + uint64(len(b.text))
			if i+1 < len(b.Funcs) {
				end = b.Funcs[i+1].Addr
			}
			b.Funcs[i].Size = end - b.Funcs[i].Addr
		}
	}
	b.loadCEnv(f)
	return b, nil
}

// lookup finds the function named sym.
func (b *Binary) lookup(sym string) (Func, error) {
	var found []Func
	for _, f := range b.Funcs {
		if f.Name == sym {
			found = append(found, f)
		}
	}
	switch len(found) {
	case 1:
		return found[0], nil
	case 0:
		var near []string
		short := sym[strings.LastIndex(sym, ".")+1:]
		for _, f := range b.Funcs {
			if strings.HasSuffix(f.Name, "."+short) && len(near) < 8 {
				near = append(near, f.Name)
			}
		}
		msg := fmt.Sprintf("No function %q in %s", sym, b.Path)
		if len(near) > 0 {
			msg += "\n  Similar: " + strings.Join(near, ", ")
		}
		msg += abi0Hint(b, sym)
		return Func{}, &diag{Msg: msg, Stage: "function selection",
			Next: "Run janus list on the binary and copy the exact symbol name. Unused functions are removed by the linker; keep them alive from main."}
	default:
		var addrs []string
		for _, f := range found {
			addrs = append(addrs, fmt.Sprintf("0x%x", f.Addr))
		}
		return Func{}, &diag{Msg: fmt.Sprintf("Symbol %q is ambiguous: %d functions at %s", sym, len(found), strings.Join(addrs, ", ")),
			Stage: "function selection", Next: "Select a function with a unique symbol name."}
	}
}

// containing returns the function whose [Addr, End) contains addr.
func (b *Binary) containing(addr uint64) (Func, bool) {
	i := sort.Search(len(b.Funcs), func(i int) bool { return b.Funcs[i].Addr > addr }) - 1
	if i >= 0 && addr < b.Funcs[i].End() {
		return b.Funcs[i], true
	}
	return Func{}, false
}

// words returns the instruction words of f with trailing zero (padding) words removed.
func (b *Binary) words(f Func) ([]uint32, error) {
	if f.Addr < b.textAddr || f.End() > b.textAddr+uint64(len(b.text)) || f.Addr%4 != 0 || f.Size%4 != 0 {
		return nil, fmt.Errorf("function %s [0x%x, 0x%x) is not a word-aligned range inside .text", f.Name, f.Addr, f.End())
	}
	raw := b.text[f.Addr-b.textAddr : f.End()-b.textAddr]
	ws := make([]uint32, len(raw)/4)
	for i := range ws {
		ws[i] = binary.LittleEndian.Uint32(raw[4*i:])
	}
	n := len(ws)
	for n > 0 && ws[n-1] == 0 {
		n--
	}
	return ws[:n], nil
}
