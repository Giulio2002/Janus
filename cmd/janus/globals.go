package main

// Writable globals with their link-time images (`janus extract --global SYM`, docs/CLI.md).
//
// A Go package variable lives in a writable section (.data/.noptrdata with an initialiser,
// .bss/.noptrbss when zero), so its contents at a call are not fixed by the binary and the
// extractor never copies it as read-only data (data.go). A theorem may still assume that a
// variable holds the value the linker gave it, the state of a program that has not written it
// (Janus.Spec.GlobalsInit). For that, --global names the symbols, and the extractor copies, byte
// for byte like read-only data, each symbol's address, size and file bytes into
// Program.globals (Janus.GlobalSegment); a .bss/.noptrbss symbol has no file bytes, and the
// loader zero-fills it. `janus check` and `janus verify` regenerate and compare the list like the
// rest of Extracted.lean.
//
// Trusted: the symbol lookup (ELF .symtab), the section and PT_LOAD checks below and the byte
// copy. Nothing else: the list does not change the run, and a theorem that does not mention
// GlobalsInit does not depend on it.

import (
	"encoding/binary"
	"fmt"
	"sort"
	"strconv"
	"strings"
)

// GlobalSeg is one writable global named by --global.
type GlobalSeg struct {
	Name    string
	Base    uint64
	Size    uint64
	Section string
	Bytes   []byte // the file bytes; nil for a NOBITS section (zero at load)
}

// globalLoad is a PT_LOAD program header (the loader view of elfview.go is loadSeg).
type globalLoad struct {
	Vaddr, Filesz, Memsz uint64
	Writable             bool
}

// collectGlobals resolves the --global patterns (exact names or globs, as for --contract) to the
// writable data symbols of b, sorted by address. Every pattern must match at least one symbol,
// and every matched symbol must lie in one writable, non-executable section that a writable
// PT_LOAD maps: file-backed (its bytes are the image) or, for .bss/.noptrbss, in the segment's
// zero-filled tail (Memsz past Filesz).
func (b *Binary) collectGlobals(pats []string) ([]GlobalSeg, error) {
	if len(pats) == 0 {
		return nil, nil
	}
	if b.SymbolSource != "symtab" {
		return nil, &diag{
			Msg:   fmt.Sprintf("--global needs the ELF symbol table, but %s has none (the pclntab names only functions)", b.Path),
			Stage: "global selection",
			Next:  "Rebuild without stripping the symbol table (no -ldflags=-s).",
		}
	}
	seen := map[string]bool{}
	var out []GlobalSeg
	add := func(g GlobalSeg) {
		if !seen[g.Name] {
			seen[g.Name] = true
			out = append(out, g)
		}
	}
	for _, p := range pats {
		base, steps, err := parseGlobalPattern(p)
		if err != nil {
			return nil, err
		}
		if len(steps) > 0 {
			// a pointer chain from one named global into the (anonymous) static data it points to
			d, ok := b.dataSymbol(base)
			if !ok {
				return nil, &diag{
					Msg:   fmt.Sprintf("--global %q: %q is not a data symbol of %s (a pointer chain starts at an exact name)", p, base, b.Path),
					Stage: "global selection",
					Next:  "Name a package variable exactly as `go tool nm` prints it.",
				}
			}
			g, err := b.globalSeg(d)
			if err != nil {
				return nil, err
			}
			add(g)
			name := base
			for _, st := range steps {
				name += st.spec
				t, err := b.derefGlobal(g, st, name)
				if err != nil {
					return nil, err
				}
				add(t)
				g = t
			}
			continue
		}
		m, err := newContractMatcher([]string{p})
		if err != nil {
			return nil, usageErr("--global needs a non-empty symbol or glob pattern")
		}
		hit := false
		for _, d := range b.dataSyms {
			if !m.match(d.Name) {
				continue
			}
			hit = true
			if seen[d.Name] {
				continue
			}
			g, err := b.globalSeg(d)
			if err != nil {
				return nil, err
			}
			add(g)
		}
		if !hit {
			return nil, &diag{
				Msg:   fmt.Sprintf("--global %q matches no data symbol of %s", p, b.Path),
				Stage: "global selection",
				Next:  "Name a package variable exactly as `go tool nm` prints it (e.g. example.com/basic.karatsubaCut).",
			}
		}
	}
	sort.SliceStable(out, func(i, j int) bool {
		if out[i].Base != out[j].Base {
			return out[i].Base < out[j].Base
		}
		return out[i].Name < out[j].Name
	})
	// Two names for one object (an alias symbol) are fine; overlapping different objects are not.
	for i := 1; i < len(out); i++ {
		a, c := out[i-1], out[i]
		if c.Base < a.Base+a.Size && !(c.Base == a.Base && c.Size == a.Size) {
			return nil, &diag{
				Msg:   fmt.Sprintf("--global: %s [0x%x, +%d) overlaps %s [0x%x, +%d)", c.Name, c.Base, c.Size, a.Name, a.Base, a.Size),
				Stage: "global selection",
				Next:  "Name only one of two overlapping symbols.",
			}
		}
	}
	return out, nil
}

// globalStep is one dereference of a --global pointer chain: the 8-byte pointer at offset Off of
// the current object's image, and the Size bytes it points to.
type globalStep struct {
	Off, Size uint64
	spec      string // "+off->size" or "->size", as written
}

// parseGlobalPattern splits a --global value into the symbol (or glob) and its pointer chain:
// NAME, or NAME followed by steps [+OFF]->SIZE (decimal or 0x hex). `math/big.intOne->32` is the
// 32-byte object intOne points to (a package-level &Int{...} is an anonymous static object that
// has no symbol of its own), `math/big.intOne->32+8->8` the 8 bytes its abs slice points to.
func parseGlobalPattern(p string) (string, []globalStep, error) {
	i := strings.Index(p, "->")
	if i < 0 {
		return p, nil, nil
	}
	base := p[:i]
	if j := strings.LastIndex(base, "+"); j >= 0 && isGlobalNum(base[j+1:]) {
		base = base[:j]
	}
	rest := p[len(base):]
	var steps []globalStep
	for rest != "" {
		var st globalStep
		k := strings.Index(rest, "->")
		if k < 0 {
			return "", nil, usageErr("--global %q: expected [+OFF]->SIZE after %q", p, p[:len(p)-len(rest)])
		}
		if k > 0 {
			if rest[0] != '+' || !isGlobalNum(rest[1:k]) {
				return "", nil, usageErr("--global %q: bad offset %q", p, rest[:k])
			}
			st.Off, _ = strconv.ParseUint(rest[1:k], 0, 64)
		}
		r := rest[k+2:]
		e := strings.IndexAny(r, "+-")
		if e < 0 {
			e = len(r)
		}
		if !isGlobalNum(r[:e]) {
			return "", nil, usageErr("--global %q: bad size %q", p, r[:e])
		}
		st.Size, _ = strconv.ParseUint(r[:e], 0, 64)
		if st.Size == 0 {
			return "", nil, usageErr("--global %q: a dereferenced object needs a positive size", p)
		}
		st.spec = rest[:k+2+e]
		steps = append(steps, st)
		rest = r[e:]
	}
	if base == "" || strings.ContainsAny(base, "*?") {
		return "", nil, usageErr("--global %q: a pointer chain starts at an exact symbol name, not a glob", p)
	}
	return base, steps, nil
}

func isGlobalNum(s string) bool {
	if s == "" {
		return false
	}
	_, err := strconv.ParseUint(s, 0, 64)
	return err == nil
}

// derefGlobal follows one step of a pointer chain from the image of g: the pointer stored at
// g.Base+st.Off at link time, and st.Size bytes there, which must be writable data (checked and
// copied like a named global, globalRange).
func (b *Binary) derefGlobal(g GlobalSeg, st globalStep, name string) (GlobalSeg, error) {
	if st.Off+8 > g.Size {
		return GlobalSeg{}, &diag{
			Msg:   fmt.Sprintf("--global %s: offset %d leaves no 8-byte pointer inside %s (%d bytes)", name, st.Off, g.Name, g.Size),
			Stage: "global selection",
			Next:  "Point at a pointer field of the object.",
		}
	}
	var ptr uint64
	if g.Bytes != nil {
		ptr = binary.LittleEndian.Uint64(g.Bytes[st.Off:])
	}
	if ptr == 0 {
		return GlobalSeg{}, &diag{
			Msg:   fmt.Sprintf("--global %s: the pointer at %s+%d is nil in the link-time image", name, g.Name, st.Off),
			Stage: "global selection",
			Next:  "A pointer chain follows only pointers the linker set.",
		}
	}
	return b.globalRange(Func{Name: name, Addr: ptr, Size: st.Size})
}

// globalSeg checks and copies one writable data symbol.
func (b *Binary) globalSeg(d Func) (GlobalSeg, error) { return b.globalRange(d) }

// globalRange checks and copies the writable range d (a data symbol, or the target of a pointer
// chain).
func (b *Binary) globalRange(d Func) (GlobalSeg, error) {
	bad := func(why string) (GlobalSeg, error) {
		return GlobalSeg{}, &diag{
			Msg:   fmt.Sprintf("--global %s (0x%x, %d bytes): %s", d.Name, d.Addr, d.Size, why),
			Stage: "global selection",
			Next:  "--global names writable package variables (.data, .noptrdata, .bss, .noptrbss); read-only data the code loads is copied as Program.data without it.",
		}
	}
	sec, ok := b.sectionOf(d.Addr)
	switch {
	case !ok:
		return bad("it is in no allocated section")
	case d.Addr+d.Size > sec.End():
		return bad(fmt.Sprintf("it extends past the end of %s", sec.Name))
	case sec.Exec:
		return bad(fmt.Sprintf("it is in the executable section %s", sec.Name))
	case !sec.Writable:
		return bad(fmt.Sprintf("it is in the read-only section %s, whose bytes the extractor copies as Program.data when the code loads them", sec.Name))
	}
	covered := false
	for _, l := range b.loads {
		if !l.Writable {
			continue
		}
		if sec.NoBits {
			// zero-filled: past the file image of the segment, inside its memory image
			covered = covered || (d.Addr >= l.Vaddr+l.Filesz && d.Addr+d.Size <= l.Vaddr+l.Memsz)
		} else {
			covered = covered || (d.Addr >= l.Vaddr && d.Addr+d.Size <= l.Vaddr+l.Filesz)
		}
	}
	if !covered {
		if sec.NoBits {
			return bad(fmt.Sprintf("no writable PT_LOAD segment zero-fills it (%s is NOBITS), so its link-time value is not known", sec.Name))
		}
		return bad(fmt.Sprintf("no writable PT_LOAD segment maps it from the file (%s)", sec.Name))
	}
	g := GlobalSeg{Name: d.Name, Base: d.Addr, Size: d.Size, Section: sec.Name}
	if !sec.NoBits {
		g.Bytes = append([]byte(nil), sec.data[d.Addr-sec.Addr:d.Addr-sec.Addr+d.Size]...)
	}
	return g, nil
}

// addGlobals records the --global symbols in x and renders Extracted.lean again (the render of an
// extraction without globals is unchanged, so earlier artifacts keep their bytes).
func (x *Extraction) addGlobals(pats []string) error {
	gs, err := x.Bin.collectGlobals(pats)
	if err != nil {
		return err
	}
	x.GlobalPatterns = append([]string(nil), pats...)
	x.Globals = gs
	if len(pats) == 0 {
		return nil
	}
	if x.Bin.GOARCH == "amd64" {
		x.Lean = renderLeanAmd64(x)
	} else {
		x.Lean = renderLean(x)
	}
	return nil
}

// extractGlobals is extractWith followed by addGlobals: the extraction `janus extract` and
// `janus check` perform.
func extractGlobals(b *Binary, sym string, maxFunctions int, contracts, globals []string, targets ...string) (*Extraction, error) {
	x, err := extractWith(b, sym, maxFunctions, contracts, targets...)
	if err != nil {
		return nil, err
	}
	if err := x.addGlobals(globals); err != nil {
		return nil, err
	}
	return x, nil
}

func writeGlobalSegment(sb *strings.Builder, g GlobalSeg, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, size := %d, init := [", leanString(g.Name), g.Base, g.Size)
	multi := len(g.Bytes) > bytesPerLine
	for j, v := range g.Bytes {
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

// writeGlobals renders `def globals` (only when --global named symbols), inline when small,
// else one definition per global (like large data objects).
func writeGlobals(sb *strings.Builder, gs []GlobalSeg) {
	total := 0
	for _, g := range gs {
		total += len(g.Bytes)
	}
	if total <= inlineWordLimit {
		sb.WriteString("def globals : List GlobalSegment := [")
		for i, g := range gs {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeGlobalSegment(sb, g, "  ")
		}
		sb.WriteString(" ]\n\n")
		return
	}
	for i, g := range gs {
		if len(g.Bytes) > segmentWordLimit {
			sb.WriteString("set_option maxRecDepth 100000 in\n")
		}
		fmt.Fprintf(sb, "def global%d : GlobalSegment :=\n  ", i)
		writeGlobalSegment(sb, g, "  ")
		sb.WriteString("\n\n")
	}
	sb.WriteString("def globals : List GlobalSegment := [")
	for i := range gs {
		if i > 0 {
			sb.WriteString(",")
			if i%wordsPerLine != 0 {
				sb.WriteString(" ")
			}
		}
		if i%wordsPerLine == 0 {
			sb.WriteString("\n  ")
		}
		fmt.Fprintf(sb, "global%d", i)
	}
	sb.WriteString(" ]\n\n")
}

// identityGlobal is a --global symbol in identity.json.
type identityGlobal struct {
	Name    string `json:"name"`
	Address string `json:"address"`
	Size    uint64 `json:"size"`
	Section string `json:"section"`
	// Sha256 of the file bytes ("" for a NOBITS section: zero at load).
	Sha256 string `json:"sha256,omitempty"`
}

func identityGlobals(gs []GlobalSeg) []identityGlobal {
	var out []identityGlobal
	for _, g := range gs {
		ig := identityGlobal{Name: g.Name, Address: hex0x(g.Base), Size: g.Size, Section: g.Section}
		if g.Bytes != nil {
			ig.Sha256 = sha256Hex(g.Bytes)
		}
		out = append(out, ig)
	}
	return out
}

// globalList renders the recorded globals as "name @ address (N bytes, section)".
func (id *Identity) globalList() []string {
	var out []string
	for _, g := range id.Globals {
		out = append(out, fmt.Sprintf("%s @ %s (%d bytes, %s)", g.Name, g.Address, g.Size, g.Section))
	}
	return out
}

// globalContaining is the --global symbol whose bytes contain addr.
func globalContaining(gs []GlobalSeg, addr uint64) (GlobalSeg, bool) {
	for _, g := range gs {
		if addr >= g.Base && addr < g.Base+g.Size {
			return g, true
		}
	}
	return GlobalSeg{}, false
}
