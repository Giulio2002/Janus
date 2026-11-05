package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"sort"
	"strings"
)

// DataSym is a data symbol (a sized, non-function ELF symbol) that the extracted code
// references. Extracted.lean names its address and size so that a proof does not hard-code
// them (docs/CLI.md, "Named data symbols").
type DataSym struct {
	Name    string // the symbol name in the binary's symbol table
	Addr    uint64
	Size    uint64
	Section string
	// Type: a type descriptor. The linker gives descriptors no ELF symbol, so Name is
	// "type:<type string>#<hash>" read from the descriptor itself (regionIdentity) and Size is
	// unknown (0, no dataSize constant is generated).
	Type bool
	// Kind: "sym" (a sized ELF symbol), "type" (a type descriptor), "anon" (anonymous data the
	// code references, named by the hash of its content: anonName), "link" (a pointer stored in
	// the link-time image of a referenced interface variable: linkWords).
	Kind  string
	Ident string // the Lean identifier component: «Name», or sym@0xADDR when that is unusable
}

// leanIdentOK reports whether s can be written inside «...» and inside a doc comment.
func leanIdentOK(s string) bool {
	if s == "" || strings.ContainsAny(s, "»«") || strings.Contains(s, "-/") || strings.Contains(s, "/-") {
		return false
	}
	for _, r := range s {
		if r < 0x20 || r == 0x7f || r == 0xfffd {
			return false
		}
	}
	return true
}

// collectDataSyms returns the data symbols the extraction references: the symbol containing
// every detected data reference (copied or skipped) and every copied data object. Sorted by
// address, then name. The set is a pure function of the extraction, like the rest of
// Extracted.lean. Identifiers are unique: a name that two different symbols share, or that
// Lean cannot spell, becomes sym@0xADDR (hex address of that symbol).
func collectDataSyms(x *Extraction) []DataSym {
	type key struct {
		name string
		addr uint64
	}
	seen := map[key]bool{}
	var out []DataSym
	refsOnly := false
	add := func(addr uint64) {
		s, ok, _ := x.Bin.dataSymbolAt(addr)
		if !ok {
			if t, ok := x.Bin.typeDescriptorAt(addr); ok {
				k := key{t, addr}
				if seen[k] {
					return
				}
				seen[k] = true
				d := DataSym{Name: t, Addr: addr, Type: true, Kind: "type"}
				if sec, ok := x.Bin.sectionOf(addr); ok {
					d.Section = sec.Name
				}
				out = append(out, d)
			} else if !refsOnly {
				// an address inside a copied window, not a reference of the code
			} else if n, ok := x.Bin.anonName(addr); ok {
				k := key{n, addr}
				if seen[k] {
					return
				}
				seen[k] = true
				sec, _ := x.Bin.sectionOf(addr)
				out = append(out, DataSym{Name: n, Addr: addr, Section: sec.Name, Type: true, Kind: "anon"})
			}
			return
		}
		k := key{s.Name, s.Addr}
		if seen[k] {
			return
		}
		seen[k] = true
		d := DataSym{Name: s.Name, Addr: s.Addr, Size: s.Size, Kind: "sym"}
		if sec, ok := x.Bin.sectionOf(s.Addr); ok {
			d.Section = sec.Name
		}
		out = append(out, d)
	}
	refsOnly = true
	for _, r := range x.DataRefs {
		add(r.Target)
	}
	for _, s := range x.Skipped {
		add(s.Target)
	}
	refsOnly = false
	for _, d := range x.Data {
		add(d.Base)
	}
	// the runtime data objects a contract's statement names (staticuint64s for slicebytetostring)
	for _, d := range x.ContractData {
		k := key{d.Name, d.Addr}
		if !seen[k] {
			seen[k] = true
			out = append(out, d)
		}
	}
	// The words of a referenced interface variable's link-time image (an `error` sentinel): its
	// type/itab word and its data pointer.
	for _, d := range append([]DataSym(nil), out...) {
		if d.Kind != "sym" {
			continue
		}
		for _, l := range x.Bin.linkWords(d) {
			k := key{l.Name, l.Addr}
			if !seen[k] {
				seen[k] = true
				out = append(out, l)
			}
		}
	}
	sort.SliceStable(out, func(i, j int) bool {
		if out[i].Addr != out[j].Addr {
			return out[i].Addr < out[j].Addr
		}
		return out[i].Name < out[j].Name
	})
	// anonymous objects whose content hashes agree: ordinal by address
	ord := map[string]int{}
	acount := map[string]int{}
	for _, d := range out {
		if d.Kind == "anon" {
			acount[d.Name]++
		}
	}
	for i := range out {
		if d := &out[i]; d.Kind == "anon" && acount[d.Name] > 1 {
			ord[d.Name]++
			d.Name = fmt.Sprintf("%s#%d", d.Name, ord[d.Name])
		}
	}
	count := map[string]int{}
	for _, d := range out {
		count[d.Name]++
	}
	for i := range out {
		d := &out[i]
		if count[d.Name] == 1 && leanIdentOK(d.Name) {
			d.Ident = d.Name
		} else {
			d.Ident = fmt.Sprintf("sym@0x%x", d.Addr)
		}
	}
	// A symbol literally named like another's fallback: disambiguate by address and index.
	seenID := map[string]bool{}
	for i := range out {
		d := &out[i]
		for seenID[d.Ident] {
			d.Ident = fmt.Sprintf("%s#%d", d.Ident, i)
		}
		seenID[d.Ident] = true
	}
	return out
}

// writeDataSyms renders `def dataAddr.«sym»` and `def dataSize.«sym»` for each symbol (nothing
// when there are none, so extractions without data references are byte-identical to earlier
// ones).
func writeDataSyms(sb *strings.Builder, syms []DataSym) {
	for _, d := range syms {
		sec := d.Section
		if sec == "" {
			sec = "?"
		}
		if d.Kind == "anon" {
			fmt.Fprintf(sb, "/-- anonymous data at 0x%x (%s), named by the hash of its first bytes -/\n", d.Addr, sec)
		} else if d.Kind == "link" {
			fmt.Fprintf(sb, "/-- a pointer word of the link-time image of an interface variable (%s) -/\n", d.Name)
		} else if d.Type && leanIdentOK(d.Name) {
			fmt.Fprintf(sb, "/-- type descriptor `%s` (%s) -/\n", d.Name, sec)
		} else if leanIdentOK(d.Name) {
			fmt.Fprintf(sb, "/-- `%s` (%s, %d bytes) -/\n", d.Name, sec, d.Size)
		} else {
			fmt.Fprintf(sb, "/-- data symbol at 0x%x (%s, %d bytes) -/\n", d.Addr, sec, d.Size)
		}
		fmt.Fprintf(sb, "def dataAddr.«%s» : Nat := 0x%x\n", d.Ident, d.Addr)
		if d.Kind == "sym" {
			fmt.Fprintf(sb, "def dataSize.«%s» : Nat := %d\n", d.Ident, d.Size)
		}
	}
	if len(syms) > 0 {
		sb.WriteString("\n")
	}
}

// typeDescriptorAt names the type descriptor that starts at addr ("type:<name>#<hash>", from
// the descriptor, as the stub pins do: typeIdentity), when addr lies in the linker's type
// region and the bytes there look like an internal/abi.Type: a valid Kind, a power-of-two
// alignment, and a printable type string. The name is only a label for the address; the address
// is the one the code computes.
func (b *Binary) typeDescriptorAt(addr uint64) (string, bool) {
	sec, ok := b.sectionOf(addr)
	if !ok || !readOnlyData(sec) || addr+48 > sec.End() {
		return "", false
	}
	types, ok := b.markerAddr("runtime.types")
	if !ok || types < sec.Addr || addr < types {
		return "", false
	}
	d := sec.data[addr-sec.Addr:]
	if k := d[23] & 31; k < 1 || k > 26 {
		return "", false
	}
	if a := d[21]; a == 0 || a&(a-1) != 0 {
		return "", false
	}
	if id, ok := b.typeIdentity(addr, sec, types); ok {
		return id, true
	}
	return "", false
}

// anonName names anonymous data (no sized symbol, not a type descriptor) that the code
// references by the content at addr, so the name survives a rebuild that moves it:
// "<section>#<8 hex digits of SHA-256>". The hashed content is the 16 bytes at addr (fewer at the
// end of the section), in which every aligned 8-byte word that is itself an address in an
// allocated section is replaced by the 16 bytes it points to (a pointer is layout, its target's
// content is not). Only file-backed, non-executable sections qualify. The name is a label: the
// address is the one the code computes.
func (b *Binary) anonName(addr uint64) (string, bool) {
	sec, ok := b.sectionOf(addr)
	if !ok || sec.Exec || sec.NoBits || sec.Name == ".gopclntab" {
		return "", false
	}
	c, ok := b.contentAt(addr, 16)
	if !ok {
		return "", false
	}
	h := sha256.New()
	h.Write([]byte("janus-anon-v1\x00"))
	h.Write([]byte(sec.Name))
	h.Write([]byte{0})
	for off := 0; off < len(c); off += 8 {
		if off+8 <= len(c) {
			w := binary.LittleEndian.Uint64(c[off:])
			if w >= 0x1000 {
				if t, ok := b.sectionOf(w); ok && !t.NoBits && !t.Exec {
					if tc, ok := b.contentAt(w, 16); ok {
						h.Write([]byte{'P'})
						h.Write(tc)
						continue
					}
				}
			}
		}
		end := min(off+8, len(c))
		h.Write([]byte{'B'})
		h.Write(c[off:end])
	}
	return fmt.Sprintf("%s#%s", sec.Name, hex.EncodeToString(h.Sum(nil))[:8]), true
}

// contentAt returns up to n bytes at addr from a file-backed section (fewer at its end).
func (b *Binary) contentAt(addr uint64, n int) ([]byte, bool) {
	sec, ok := b.sectionOf(addr)
	if !ok || sec.NoBits || addr-sec.Addr >= uint64(len(sec.data)) {
		return nil, false
	}
	d := sec.data[addr-sec.Addr:]
	if len(d) > n {
		d = d[:n]
	}
	return d, true
}

// linkWords: when d is a 16-byte referenced data symbol whose link-time image is an interface
// value (word 0 a type descriptor or a static itab, word 1 a pointer into an allocated section),
// its two words as constants named "<symbol>→type" and "<symbol>→data". These are the values the
// binary stores in the variable's initial image (an `error` sentinel: the `errors.New` result
// built at link time); a proof that states the variable's contents needs them. Nothing for a
// symbol that is not such a value.
func (b *Binary) linkWords(d DataSym) []DataSym {
	if d.Size != 16 || !leanIdentOK(d.Name) {
		return nil
	}
	c, ok := b.contentAt(d.Addr, 16)
	if !ok || len(c) != 16 {
		return nil
	}
	if sec, ok := b.sectionOf(d.Addr); !ok || sec.Exec {
		return nil
	}
	w0, w1 := binary.LittleEndian.Uint64(c), binary.LittleEndian.Uint64(c[8:])
	isItab := false
	if s, ok, _ := b.dataSymbolAt(w0); ok && s.Addr == w0 && strings.HasPrefix(s.Name, itabPrefix) {
		isItab = true
	}
	if _, ok := b.typeDescriptorAt(w0); !ok && !isItab {
		return nil
	}
	if t, ok := b.sectionOf(w1); !ok || t.Exec || w1 < 0x1000 {
		return nil
	}
	return []DataSym{
		{Name: d.Name + "→type", Addr: w0, Section: d.Section, Kind: "link", Type: true},
		{Name: d.Name + "→data", Addr: w1, Section: d.Section, Kind: "link", Type: true},
	}
}

// contractDataSyms maps a contract function to the runtime data object its Janus/Contracts statement names. The
// object's address is a parameter of the contract (`slicebytetostringSpec st`): `n = 1` returns
// `&runtime.staticuint64s[*ptr]`, an object of the binary, not runtime-allocated. The extractor checks the symbol
// (present, 2048 bytes, in a read-only section, contents `staticuint64s[i] = i`) and names its address in
// Extracted.lean; the auditor accepts no other argument for the spec.
var contractDataSyms = map[string]string{"runtime.slicebytetostring": "runtime.staticuint64s"}

// staticuint64sTable is the contents of runtime.staticuint64s: the little-endian words 0, 1, …, 255.
func staticuint64sTable() []byte {
	t := make([]byte, 256*8)
	for i := 0; i < 256; i++ {
		binary.LittleEndian.PutUint64(t[8*i:], uint64(i))
	}
	return t
}

// checkContractData finds the data symbol sym a contract for fn names and checks it is the Go runtime's.
func (b *Binary) checkContractData(fn, sym string) (DataSym, error) {
	bad := func(why string) (DataSym, error) {
		return DataSym{}, &diag{
			Msg:   fmt.Sprintf("--contract names %s, whose framework contract takes the address of %s, but %s", fn, sym, why),
			Stage: "code extraction",
			Next:  "Build with a Go toolchain whose runtime has this table (Go 1.26) and without stripping the symbol table (no -ldflags=-s).",
		}
	}
	s, ok := b.dataSymbol(sym)
	if !ok {
		return bad("the binary has no such data symbol")
	}
	if s.Size != 256*8 {
		return bad(fmt.Sprintf("the symbol at 0x%x has size %d, not 2048", s.Addr, s.Size))
	}
	sec, ok := b.sectionOf(s.Addr)
	if !ok || sec.Writable {
		return bad(fmt.Sprintf("the symbol at 0x%x is not in a read-only section", s.Addr))
	}
	bs, ok := b.readAt(s.Addr, s.Size)
	if !ok || !bytes.Equal(bs, staticuint64sTable()) {
		return bad(fmt.Sprintf("the 2048 bytes at 0x%x are not the table 0, 1, …, 255", s.Addr))
	}
	return DataSym{Name: s.Name, Addr: s.Addr, Size: s.Size, Section: sec.Name, Kind: "sym"}, nil
}
