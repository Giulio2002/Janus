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
		// ENDBR64 (F3 0F 1E FA), which C compilers emit at function entries; this x86asm
		// version decodes it as a 3-byte REP-prefixed instruction followed by CLI.
		if off+4 <= len(code) && code[off] == 0xF3 && code[off+1] == 0x0F && code[off+2] == 0x1E && code[off+3] == 0xFA {
			out = append(out, amd64Inst{PC: base + uint64(off), Inst: x86asm.Inst{Op: x86asm.NOP, Len: 4}})
			off += 4
			continue
		}
		// ADCX/ADOX (66/F3 [REX] 0F 38 F6 /r), which this x86asm version does not know: swept
		// with the operands of ADC r, r/m (13 /r) and their own length, so that the sweep stays
		// in step and finds their RIP-relative operands
		if inst, ok := decodeADX(code[off:]); ok {
			out = append(out, amd64Inst{PC: base + uint64(off), Inst: inst})
			off += inst.Len
			continue
		}
		inst, err := x86asm.Decode(code[off:], 64)
		if err != nil || inst.Len == 0 || inst.Op == 0 || code[off] == 0x62 {
			// EVEX (AVX-512, which this x86asm does not know at all) and the VEX encodings it
			// does not know (the opmask instructions): length from the encoding, and a
			// RIP-relative operand kept for the data references
			if n, disp, rip := vexLenRIP(code[off:]); n > 0 {
				in := x86asm.Inst{Len: n}
				if rip {
					in.Args[0] = x86asm.Mem{Base: x86asm.RIP, Disp: disp}
				}
				out = append(out, amd64Inst{PC: base + uint64(off), Inst: in})
				off += n
				continue
			}
			if err != nil || inst.Len == 0 {
				off++
				continue
			}
		}
		out = append(out, amd64Inst{PC: base + uint64(off), Inst: inst})
		off += inst.Len
	}
	return out
}

// decodeADX decodes ADCX (66 [REX] 0F 38 F6 /r) or ADOX (F3 [REX] 0F 38 F6 /r), legacy
// prefixes other than 66/F2/F3 allowed before REX, as the ADC r32/64, r/m32/64 with the same
// operands, Len set to the instruction's length.
func decodeADX(b []byte) (x86asm.Inst, bool) {
	var keep []byte
	has66, rep, removed := false, byte(0), 0
	i := 0
loop:
	for ; i < len(b) && i < 15; i++ {
		switch c := b[i]; c {
		case 0x66:
			has66 = true
			removed++
		case 0xF2, 0xF3:
			rep = c
			removed++
		case 0x26, 0x2E, 0x36, 0x3E, 0x64, 0x65, 0x67, 0xF0:
			keep = append(keep, c)
		default:
			break loop
		}
	}
	if i < len(b) && b[i]&0xF0 == 0x40 {
		keep = append(keep, b[i])
		i++
	}
	if i+3 > len(b) || b[i] != 0x0F || b[i+1] != 0x38 || b[i+2] != 0xF6 {
		return x86asm.Inst{}, false
	}
	if !(has66 && rep == 0) && !(!has66 && rep == 0xF3) {
		return x86asm.Inst{}, false
	}
	alt, err := x86asm.Decode(append(append(keep, 0x13), b[i+3:]...), 64)
	if err != nil || alt.Op != x86asm.ADC {
		return x86asm.Inst{}, false
	}
	alt.Len += removed + 2
	return alt, true
}

// vexLenRIP is the length of a VEX (C4/C5) or EVEX (62) instruction at b that x86asm cannot
// decode (0 if b is not one), and its RIP-relative displacement (mod = 00, r/m = 101: disp32,
// never compressed). An imm8 follows in map 3 and for the map-1 opcodes 70-73, C2, C4-C6.
// Untrusted, like the rest of the sweep: Lean decodes every instruction again.
func vexLenRIP(b []byte) (int, int64, bool) {
	if len(b) < 3 {
		return 0, 0, false
	}
	var mp, n int
	switch b[0] {
	case 0xC5:
		mp, n = 1, 2
	case 0xC4:
		mp, n = int(b[1]&0x1F), 3
	case 0x62:
		if len(b) < 4 {
			return 0, 0, false
		}
		mp, n = int(b[1]&0x07), 4
	default:
		return 0, 0, false
	}
	if len(b) < n+2 {
		return 0, 0, false
	}
	op, modrm := b[n], b[n+1]
	l := n + 2
	mod, rm := modrm>>6, modrm&7
	rip := false
	var disp int64
	if mod != 3 {
		if rm == 4 {
			if len(b) <= l {
				return 0, 0, false
			}
			sib := b[l]
			l++
			if mod == 0 && sib&7 == 5 {
				l += 4
			}
		}
		switch mod {
		case 0:
			if rm == 5 {
				if len(b) < l+4 {
					return 0, 0, false
				}
				rip = true
				disp = int64(int32(uint32(b[l]) | uint32(b[l+1])<<8 | uint32(b[l+2])<<16 | uint32(b[l+3])<<24))
				l += 4
			}
		case 1:
			l++
		case 2:
			l += 4
		}
	}
	if mp == 3 || mp == 1 && (op >= 0x70 && op <= 0x73 || op == 0xC2 || op == 0xC4 || op == 0xC5 || op == 0xC6) {
		l++
	}
	if l > len(b) || l > 15 {
		return 0, 0, false
	}
	return l, disp, rip
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

// extractAmd64Func copies one amd64 function and lists its direct branches.
func extractAmd64Func(b *Binary, f Func) (Segment, []Unresolved, error) {
	code, err := b.codeBytes(f)
	if err != nil {
		return Segment{}, nil, err
	}
	var brs []Unresolved
	for _, in := range sweepAmd64(code, f.Addr) {
		if t, ok := amd64BranchTarget(in); ok {
			brs = append(brs, Unresolved{From: in.PC, Target: t})
		}
	}
	return Segment{Name: f.Name, Base: f.Addr, Size: f.Size, Bytes: code}, brs, nil
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
	writeProgram(&sb, x, "Amd64.Program")
	fmt.Fprintf(&sb, "def entry : Nat := 0x%x\n\n", x.Entry.Addr)
	sb.WriteString("end Extracted\n")
	return []byte(sb.String())
}
