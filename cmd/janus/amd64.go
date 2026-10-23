package main

// GOARCH=amd64 extraction: byte segments for the Lean x86-64 runner (`Janus.Amd64.Program`).
//
// As for arm64, the trusted part is the copy: the raw bytes of the function symbol's
// [Addr, Addr+Size) range of .text, including the INT3 (0xCC) padding after the last
// instruction (the Lean decoder rejects INT3, so padding can never be executed as something
// else, and nothing has to decide where the last instruction ends). Lean decodes every
// instruction again from these bytes.
//
// Untrusted: reachability and data-reference detection, a linear sweep with
// golang.org/x/arch/x86/x86asm. A missed callee is absent from the program (the model faults
// with noCode there); a missed data reference is absent from Program.data (the access
// faults). Neither can make a false theorem provable.

import (
	"fmt"
	"strings"

	"golang.org/x/arch/x86/x86asm"
)

// codeBytes returns the bytes of f.
func (b *Binary) codeBytes(f Func) ([]byte, error) {
	if f.Addr < b.textAddr || f.End() > b.textAddr+uint64(len(b.text)) || f.End() < f.Addr {
		return nil, fmt.Errorf("function %s [0x%x, 0x%x) is not a range inside .text", f.Name, f.Addr, f.End())
	}
	return append([]byte(nil), b.text[f.Addr-b.textAddr:f.End()-b.textAddr]...), nil
}

// amd64Inst is one instruction of the linear sweep.
type amd64Inst struct {
	PC   uint64
	Inst x86asm.Inst
}

// sweepAmd64 decodes code (at address base) linearly; undecodable bytes are skipped one at
// a time.
func sweepAmd64(code []byte, base uint64) []amd64Inst {
	var out []amd64Inst
	for off := 0; off < len(code); {
		inst, err := x86asm.Decode(code[off:], 64)
		if err != nil || inst.Len == 0 {
			off++
			continue
		}
		out = append(out, amd64Inst{PC: base + uint64(off), Inst: inst})
		off += inst.Len
	}
	return out
}

// amd64BranchTarget returns the target of a direct (relative) JMP, Jcc, CALL, LOOP or
// JRCXZ.
func amd64BranchTarget(in amd64Inst) (uint64, bool) {
	for _, a := range in.Inst.Args {
		if a == nil {
			break
		}
		if rel, ok := a.(x86asm.Rel); ok {
			return uint64(int64(in.PC) + int64(in.Inst.Len) + int64(rel)), true
		}
	}
	return 0, false
}

// amd64DataRefs finds RIP-relative memory operands: LEA reg, [rip+disp] ("rip-lea") and
// loads/stores through [rip+disp] ("rip-mem"). The target is the next instruction's address
// plus disp.
func amd64DataRefs(insts []amd64Inst) []DataRef {
	var refs []DataRef
	for _, in := range insts {
		for _, a := range in.Inst.Args {
			if a == nil {
				break
			}
			m, ok := a.(x86asm.Mem)
			if !ok || m.Base != x86asm.RIP || m.Index != 0 || m.Segment != 0 {
				continue
			}
			kind := "rip-mem"
			if in.Inst.Op == x86asm.LEA {
				kind = "rip-lea"
			}
			refs = append(refs, DataRef{From: in.PC, Target: uint64(int64(in.PC) + int64(in.Inst.Len) + m.Disp), Kind: kind})
		}
	}
	return refs
}

// extractAmd64 is extractFrom for amd64 binaries: entry plus every function reachable by
// direct branches, breadth first.
func extractAmd64(b *Binary, entry Func, maxFunctions int) (*Extraction, error) {
	x := &Extraction{Bin: b, Entry: entry}
	seen := map[uint64]bool{entry.Addr: true}
	stubSeen := map[uint64]bool{}
	queue := []Func{entry}
	var sweeps [][]amd64Inst
	for len(queue) > 0 {
		f := queue[0]
		queue = queue[1:]
		code, err := b.codeBytes(f)
		if err != nil {
			return nil, &diag{Msg: err.Error(), Stage: "code extraction", Next: "Report this binary layout to the Janus maintainers."}
		}
		x.Segments = append(x.Segments, Segment{Name: f.Name, Base: f.Addr, Size: f.Size, Bytes: code})
		insts := sweepAmd64(code, f.Addr)
		sweeps = append(sweeps, insts)
		for _, in := range insts {
			t, ok := amd64BranchTarget(in)
			if !ok || (t >= f.Addr && t < f.End()) {
				continue
			}
			g, ok := b.containing(t)
			if !ok {
				x.Unresolved = append(x.Unresolved, Unresolved{From: in.PC, Target: t})
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
	for _, insts := range sweeps {
		x.DataRefs = append(x.DataRefs, amd64DataRefs(insts)...)
	}
	x.Data, x.Skipped = collectData(b, x.DataRefs)
	x.Lean = renderLeanAmd64(x)
	return x, nil
}

// Thresholds for splitting the rendered program, as for arm64 words (see renderLean).
const (
	amd64InlineByteLimit  = 8192
	amd64SegmentByteLimit = 4096
)

func writeAmd64Segment(sb *strings.Builder, s Segment, indent string) {
	fmt.Fprintf(sb, "{ name := %s, base := 0x%x, bytes := [", leanString(s.Name), s.Base)
	multi := len(s.Bytes) > bytesPerLine
	for j, v := range s.Bytes {
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

// renderLeanAmd64 produces Extracted.lean for an amd64 extraction (a `Janus.Amd64.Program`).
func renderLeanAmd64(x *Extraction) []byte {
	var sb strings.Builder
	sb.WriteString("import Janus\n\n")
	fmt.Fprintf(&sb, "/-! Generated by `janus extract` %s from `%s` (%s, %s, %s/%s).\n", extractorVersion, x.Entry.Name,
		x.Bin.MainModule, x.Bin.GoVersion, x.Bin.GOOS, x.Bin.GOARCH)
	sb.WriteString("Do not edit: `janus check` regenerates this file from the binary and compares it byte for byte.\n")
	sb.WriteString("The binary's SHA-256 is recorded in `identity.json`. -/\n\n")
	sb.WriteString("namespace Extracted\nopen Janus\n\n")
	total := 0
	for _, s := range x.Segments {
		total += len(s.Bytes)
	}
	if total <= amd64InlineByteLimit {
		sb.WriteString("def segments : List Amd64.Segment := [")
		for i, s := range x.Segments {
			if i > 0 {
				sb.WriteString(",")
			}
			sb.WriteString("\n  ")
			writeAmd64Segment(&sb, s, "  ")
		}
		sb.WriteString(" ]\n\n")
	} else {
		for i, s := range x.Segments {
			if len(s.Bytes) > amd64SegmentByteLimit {
				sb.WriteString("set_option maxRecDepth 100000 in\n")
			}
			fmt.Fprintf(&sb, "def seg%d : Amd64.Segment :=\n  ", i)
			writeAmd64Segment(&sb, s, "  ")
			sb.WriteString("\n\n")
		}
		sb.WriteString("def segments : List Amd64.Segment := [")
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
		sb.WriteString("def program : Amd64.Program := { segments := segments, stubs := stubs, exitAddr := exitAddr }\n\n")
	} else {
		writeData(&sb, x.Data)
		sb.WriteString("def program : Amd64.Program :=\n  { segments := segments, stubs := stubs, exitAddr := exitAddr, data := data }\n\n")
	}
	fmt.Fprintf(&sb, "def entry : Nat := 0x%x\n\n", x.Entry.Addr)
	sb.WriteString("end Extracted\n")
	return []byte(sb.String())
}
