package main

import (
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
	Type  bool
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
	add := func(addr uint64) {
		s, ok, _ := x.Bin.dataSymbolAt(addr)
		if !ok {
			if t, ok := x.Bin.typeDescriptorAt(addr); ok {
				k := key{t, addr}
				if seen[k] {
					return
				}
				seen[k] = true
				d := DataSym{Name: t, Addr: addr, Type: true}
				if sec, ok := x.Bin.sectionOf(addr); ok {
					d.Section = sec.Name
				}
				out = append(out, d)
			}
			return
		}
		k := key{s.Name, s.Addr}
		if seen[k] {
			return
		}
		seen[k] = true
		d := DataSym{Name: s.Name, Addr: s.Addr, Size: s.Size}
		if sec, ok := x.Bin.sectionOf(s.Addr); ok {
			d.Section = sec.Name
		}
		out = append(out, d)
	}
	for _, r := range x.DataRefs {
		add(r.Target)
	}
	for _, s := range x.Skipped {
		add(s.Target)
	}
	for _, d := range x.Data {
		add(d.Base)
	}
	sort.SliceStable(out, func(i, j int) bool {
		if out[i].Addr != out[j].Addr {
			return out[i].Addr < out[j].Addr
		}
		return out[i].Name < out[j].Name
	})
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
		if d.Type && leanIdentOK(d.Name) {
			fmt.Fprintf(sb, "/-- type descriptor `%s` (%s) -/\n", d.Name, sec)
		} else if leanIdentOK(d.Name) {
			fmt.Fprintf(sb, "/-- `%s` (%s, %d bytes) -/\n", d.Name, sec, d.Size)
		} else {
			fmt.Fprintf(sb, "/-- data symbol at 0x%x (%s, %d bytes) -/\n", d.Addr, sec, d.Size)
		}
		fmt.Fprintf(sb, "def dataAddr.«%s» : Nat := 0x%x\n", d.Ident, d.Addr)
		if !d.Type {
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
