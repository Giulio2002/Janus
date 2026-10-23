// Package gen builds x86-64 test cases: targeted random encodings per opcode, fully random
// prefix/opcode byte strings, and initial states steered so that memory operands land in
// the data buffer and branch targets in the code page. x86asm (golang.org/x/arch) is used
// only to classify and to find operands for steering; it never decides a verdict.
package gen

import (
	"encoding/hex"
	"fmt"
	"math/rand/v2"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// State is a complete initial state (memory beyond the pattern given by Init overrides).
type State struct {
	Regs   [16]uint64
	RFlags int
	XMM    [16][2]uint64 // lo, hi
	Seed   uint64
	Init   [][2]int // buffer byte overrides (offset, value)
}

func hex64(v uint64) string { return fmt.Sprintf("%#x", v) }

func hex128(lo, hi uint64) string {
	if hi == 0 {
		return fmt.Sprintf("%#x", lo)
	}
	return fmt.Sprintf("0x%x%016x", hi, lo)
}

// Case renders a test case.
func Case(id int, class string, b []byte, s State) L.Case {
	c := L.Case{ID: id, Class: class, Bytes: hex.EncodeToString(b), RFlags: s.RFlags & L.StatusFlags, Seed: s.Seed, Init: s.Init}
	for i := 0; i < 16; i++ {
		c.Regs[i] = hex64(s.Regs[i])
		c.XMM[i] = hex128(s.XMM[i][0], s.XMM[i][1])
	}
	return c
}

// Decode decodes b in 64-bit mode.
func Decode(b []byte) (x86asm.Inst, bool) {
	inst, err := x86asm.Decode(b, 64)
	// x86asm reports a prefix followed by an undecodable opcode as a 1-byte Op(0).
	return inst, err == nil && inst.Op != 0
}

// Asm is GNU-syntax disassembly at TestPC ("(bad)" if x86asm cannot decode).
func Asm(b []byte) string {
	inst, ok := Decode(b)
	if !ok {
		return "(bad)"
	}
	s := x86asm.GNUSyntax(inst, L.TestPC, nil)
	if inst.Len < len(b) {
		s += fmt.Sprintf(" [+%d bytes]", len(b)-inst.Len)
	}
	return s
}

var condOps = map[x86asm.Op]string{}

func init() {
	for _, op := range []x86asm.Op{x86asm.JA, x86asm.JAE, x86asm.JB, x86asm.JBE, x86asm.JE, x86asm.JG, x86asm.JGE,
		x86asm.JL, x86asm.JLE, x86asm.JNE, x86asm.JNO, x86asm.JNP, x86asm.JNS, x86asm.JO, x86asm.JP, x86asm.JS} {
		condOps[op] = "jcc"
	}
	for _, op := range []x86asm.Op{x86asm.SETA, x86asm.SETAE, x86asm.SETB, x86asm.SETBE, x86asm.SETE, x86asm.SETG, x86asm.SETGE,
		x86asm.SETL, x86asm.SETLE, x86asm.SETNE, x86asm.SETNO, x86asm.SETNP, x86asm.SETNS, x86asm.SETO, x86asm.SETP, x86asm.SETS} {
		condOps[op] = "setcc"
	}
	for _, op := range []x86asm.Op{x86asm.CMOVA, x86asm.CMOVAE, x86asm.CMOVB, x86asm.CMOVBE, x86asm.CMOVE, x86asm.CMOVG, x86asm.CMOVGE,
		x86asm.CMOVL, x86asm.CMOVLE, x86asm.CMOVNE, x86asm.CMOVNO, x86asm.CMOVNP, x86asm.CMOVNS, x86asm.CMOVO, x86asm.CMOVP, x86asm.CMOVS} {
		condOps[op] = "cmovcc"
	}
}

// Modeled lists the mnemonics (x86asm names, lower case) of the integer subset the Lean
// model is meant to cover; the rest are "other" (still run, the model should reject them).
var Modeled = map[string]bool{}

func init() {
	for _, m := range strings.Fields(`add or adc sbb and sub xor cmp test mov movzx movsx movsxd lea inc dec not neg
		mul imul div idiv rol ror shl shr sar shld shrd bt bts btr btc bsf bsr tzcnt lzcnt popcnt bswap
		setcc cmovcc jcc jmp call ret push pop nop xchg cbw cwde cdqe cwd cdq cqo clc stc cmc leave
		movups movupd movaps movapd movdqu movdqa xorps xorpd pxor movd movq ud2 int3 int`) {
		Modeled[m] = true
	}
}

// Classify names the instruction class: the x86asm mnemonic in lower case (jcc/setcc/cmovcc
// grouped), "invalid" if x86asm cannot decode it.
func Classify(b []byte) string {
	inst, ok := Decode(b)
	if !ok {
		return "invalid"
	}
	if c, ok := condOps[inst.Op]; ok {
		return c
	}
	return strings.ToLower(inst.Op.String())
}

// Conditional classes read the status flags; they run under several flag combinations.
func Conditional(cls string) bool {
	switch cls {
	case "jcc", "setcc", "cmovcc", "adc", "sbb", "cmc", "rcl", "rcr":
		return true
	}
	return false
}

// RandFlags returns a uniformly random combination of the six status flags.
func RandFlags(r *rand.Rand) int {
	bits := []int{L.FlagCF, L.FlagPF, L.FlagAF, L.FlagZF, L.FlagSF, L.FlagOF}
	f := 0
	for _, b := range bits {
		if r.IntN(2) == 1 {
			f |= b
		}
	}
	return f
}

// FlagCombo returns combination k (0..63) of the six status flags.
func FlagCombo(k int) int {
	bits := []int{L.FlagCF, L.FlagPF, L.FlagAF, L.FlagZF, L.FlagSF, L.FlagOF}
	f := 0
	for i, b := range bits {
		if k>>i&1 == 1 {
			f |= b
		}
	}
	return f
}

var edges = []uint64{0, 1, 2, 3, 7, 8, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x10000,
	0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
	0xffffffffffffffff, 0xfffffffffffffffe, 0x8000000000000001, 0x00000000ffffff00, 63, 64, 65, 31, 32, 33, 15, 16, 17}

// RandValue mixes edge values, random 64/32/16/8-bit values, small signed values and buffer
// pointers.
func RandValue(r *rand.Rand) uint64 {
	switch r.IntN(8) {
	case 0, 1:
		return edges[r.IntN(len(edges))]
	case 2:
		return r.Uint64()
	case 3:
		return uint64(r.Uint32())
	case 4:
		return uint64(int64(r.IntN(65)) - 32)
	case 5:
		return L.DataBase + uint64(r.IntN(L.DataSize))
	case 6:
		return uint64(r.IntN(1 << 16))
	default:
		v := r.Uint64()
		if r.IntN(2) == 0 {
			v |= 1 << 63
		}
		return v >> uint(r.IntN(64))
	}
}

// regNum maps an x86asm register to (GPR number, ok); 8-bit high registers map to their
// full register with hi = true.
func regNum(a x86asm.Reg) (n int, hi bool, ok bool) {
	switch {
	case a >= x86asm.AL && a <= x86asm.BL:
		return int(a - x86asm.AL), false, true
	case a >= x86asm.AH && a <= x86asm.BH:
		return int(a - x86asm.AH), true, true
	case a >= x86asm.SPB && a <= x86asm.R15B:
		return int(a-x86asm.SPB) + 4, false, true
	case a >= x86asm.AX && a <= x86asm.R15W:
		return int(a - x86asm.AX), false, true
	case a >= x86asm.EAX && a <= x86asm.R15L:
		return int(a - x86asm.EAX), false, true
	case a >= x86asm.RAX && a <= x86asm.R15:
		return int(a - x86asm.RAX), false, true
	}
	return 0, false, false
}

// Setup returns a random initial state for instruction b, steered by its operands.
func Setup(r *rand.Rand, b []byte) State {
	var s State
	for i := range s.Regs {
		s.Regs[i] = RandValue(r)
	}
	for i := range s.XMM {
		switch r.IntN(4) {
		case 0:
			s.XMM[i] = [2]uint64{0, 0}
		case 1:
			s.XMM[i] = [2]uint64{RandValue(r), RandValue(r)}
		default:
			s.XMM[i] = [2]uint64{r.Uint64(), r.Uint64()}
		}
	}
	// RSP: mostly an 8-aligned pointer into the middle of the buffer.
	switch r.IntN(10) {
	case 0:
		s.Regs[4] = RandValue(r)
	case 1:
		s.Regs[4] = L.DataBase + uint64(r.IntN(L.DataSize))
	default:
		s.Regs[4] = L.DataBase + 1024 + 8*uint64(r.IntN(256))
	}
	s.RFlags = RandFlags(r)
	s.Seed = uint64(r.IntN(1 << 20))
	inst, ok := Decode(b)
	if !ok {
		return s
	}
	cls := Classify(b)
	for _, a := range inst.Args {
		if a == nil {
			break
		}
		switch a := a.(type) {
		case x86asm.Mem:
			steerMem(r, &s, inst, a)
		case x86asm.Reg:
			if (cls == "jmp" || cls == "call") && r.IntN(10) < 7 {
				if n, _, ok := regNum(a); ok {
					s.Regs[n] = codeTarget(r)
				}
			}
			// shift counts in CL: bias to interesting counts
			if a == x86asm.CL && r.IntN(2) == 0 {
				s.Regs[1] = s.Regs[1]&^0xff | uint64(edgesCount[r.IntN(len(edgesCount))])
			}
		}
	}
	switch cls {
	case "ret", "pop", "leave":
		// put a plausible return address / value at the top of the stack
		if r.IntN(10) < 7 {
			sp := s.Regs[4]
			if cls == "leave" {
				sp = s.Regs[5]
			}
			if sp >= L.DataBase && sp <= L.DataBase+L.DataSize-8 {
				v := codeTarget(r)
				if r.IntN(3) == 0 {
					v = RandValue(r)
				}
				for k := 0; k < 8; k++ {
					s.Init = append(s.Init, [2]int{int(sp - L.DataBase + uint64(k)), int(v >> (8 * k) & 0xff)})
				}
			}
		}
	}
	return s
}

var edgesCount = []int{0, 1, 2, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 0xff}

// codeTarget is mostly an address in the code page, sometimes far or non-canonical.
func codeTarget(r *rand.Rand) uint64 {
	switch r.IntN(10) {
	case 0:
		return 0x7700_0000_0000 + uint64(r.IntN(1<<20))
	case 1:
		return 0x8000_0000_0000 + uint64(r.IntN(1<<20)) // non-canonical
	case 2:
		return L.DataBase + uint64(r.IntN(L.DataSize)) // mapped, not executable
	default:
		return L.CodePage + uint64(r.IntN(L.PageSize))
	}
}

// steerMem sets the base (or index) register so the effective address mostly lands inside
// the buffer, sometimes straddles one of its ends, sometimes is wild.
func steerMem(r *rand.Rand, s *State, inst x86asm.Inst, m x86asm.Mem) {
	if m.Base == x86asm.RIP || m.Segment == x86asm.FS || m.Segment == x86asm.GS {
		return
	}
	size := inst.MemBytes
	if size <= 0 {
		size = 8
	}
	var target uint64
	switch k := r.IntN(20); {
	case k < 16:
		lo := 0
		hi := L.DataSize - size
		if r.IntN(3) == 0 && hi > 0 {
			// aligned to the access size
			target = L.DataBase + uint64(r.IntN(hi/size+1)*size)
		} else {
			target = L.DataBase + uint64(lo+r.IntN(hi+1))
		}
	case k < 18:
		if r.IntN(2) == 0 {
			target = L.DataBase - uint64(1+r.IntN(size))
		} else {
			target = L.DataBase + L.DataSize - uint64(r.IntN(size))
		}
	default:
		return
	}
	scale := uint64(m.Scale)
	if scale == 0 {
		scale = 1
	}
	bn, _, bok := regNum(m.Base)
	in, _, iok := regNum(m.Index)
	disp := uint64(m.Disp)
	if inst.AddrSize == 32 {
		// 32-bit addressing: the effective address is truncated to 32 bits; the buffer is
		// above 4 GiB, so it cannot be reached. Leave it wild.
		return
	}
	switch {
	case bok && iok && bn == in:
		v := target - disp
		if v%(1+scale) == 0 {
			s.Regs[bn] = v / (1 + scale)
		}
	case bok && iok:
		if bn == 4 {
			// keep RSP a sane stack pointer when it is the base; move the index
			if r.IntN(2) == 0 {
				s.Regs[4] = L.DataBase + 1024 + 8*uint64(r.IntN(256))
			}
			off := target - disp - s.Regs[4]
			if off%scale == 0 {
				s.Regs[in] = off / scale
			}
			return
		}
		s.Regs[in] = uint64(int64(r.IntN(33) - 16))
		s.Regs[bn] = target - disp - s.Regs[in]*scale
	case bok:
		s.Regs[bn] = target - disp
	case iok:
		v := target - disp
		if v%scale == 0 {
			s.Regs[in] = v / scale
		}
	}
}
