package gen

import (
	"fmt"
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// AVX-512 (WP-G): EVEX-encoded instructions with the ZMM/opmask state, the VEX opmask
// instructions and the VEX forms of VPCLMULQDQ and GFNI, Janus/Amd64/{InstrEVEX,DecodeEVEX,
// ExecEVEX}.lean. x86asm does not decode EVEX, so the generator steers the operands from its own
// knowledge of the encoding (Evex512Targeted records the fields it drew).

// Tuple types (disp8*N, SDM Vol. 2 §2.7.5).
const (
	tFV   = iota // full vector: N = l/8, or the element with a broadcast
	tFVM         // full vector, no broadcast
	tT1S         // one element (N = e/8)
	tM128        // 16 bytes
	tT4          // a 128-bit chunk (N = 16)
	tT8          // a 256-bit chunk (N = 32)
	tPMOV        // VPMOVSX/ZX: N = l*f/t/8 (f/t in the spec's elem fields)
	tNone        // VEX: no compression
)

// EvexSpec is a targeted EVEX (or, Vex = true, VEX) family.
type EvexSpec struct {
	Name     string
	Map, PP  byte
	Op       byte
	Ext      int  // ModRM.reg opcode extension (-1: a register operand)
	W        int  // 0, 1, or -1 (both)
	Mod      int  // 0 any, 1 register only, 2 memory only
	Imm      bool // an imm8 follows
	NDS      bool // vvvv is an operand
	Tuple    int
	E        int // element width (D/Q forms: E = 32 for W0, 64 for W1 when EW)
	EW       bool
	KReg     bool // ModRM.reg is a mask register (compares)
	Vex      bool
	ImmLimit int // draw imm8 below this (0: any)
}

func evexSpecs() []EvexSpec {
	var s []EvexSpec
	// helper constructors
	ev := func(name string, mp, pp, op byte, w int, nds bool, tuple, e int, ew bool) EvexSpec {
		return EvexSpec{Name: name, Map: mp, PP: pp, Op: op, Ext: -1, W: w, NDS: nds, Tuple: tuple, E: e, EW: ew}
	}
	// map 1: moves
	for _, op := range []byte{0x10, 0x11, 0x28, 0x29} {
		s = append(s, ev("evex/movps", 1, 0, op, 0, false, tFVM, 32, false))
		s = append(s, ev("evex/movpd", 1, 1, op, 1, false, tFVM, 64, false))
	}
	for _, op := range []byte{0x6F, 0x7F} {
		s = append(s, ev("evex/movdqa", 1, 1, op, -1, false, tFVM, 32, true))
		s = append(s, ev("evex/movdqu32", 1, 2, op, -1, false, tFVM, 32, true))
		s = append(s, ev("evex/movdqu8", 1, 3, op, -1, false, tFVM, 8, false))
	}
	// map 1: FP
	for _, op := range []byte{0x51, 0x58, 0x59, 0x5C, 0x5D, 0x5E, 0x5F, 0x54, 0x55, 0x56, 0x57} {
		s = append(s, ev("evex/fpps", 1, 0, op, 0, op != 0x51, tFV, 32, false))
		s = append(s, ev("evex/fppd", 1, 1, op, 1, op != 0x51, tFV, 64, false))
	}
	for pp := byte(0); pp < 2; pp++ {
		sp := ev("evex/fpcmp", 1, pp, 0xC2, int(pp), true, tFV, 32<<pp, false)
		sp.Imm, sp.KReg, sp.ImmLimit = true, true, 40
		s = append(s, sp)
	}
	// map 1, 66: integer
	for _, op := range []byte{0xDB, 0xDF, 0xEB, 0xEF, 0xFE, 0xD4, 0xFA, 0xFB, 0xF4, 0x62, 0x6A, 0x6C, 0x6D, 0x6B} {
		s = append(s, ev("evex/int", 1, 1, op, -1, true, tFV, 32, true))
	}
	for _, op := range []byte{0xFC, 0xFD, 0xF8, 0xF9, 0xEC, 0xED, 0xDC, 0xDD, 0xE8, 0xE9, 0xD8, 0xD9, 0xE0,
		0xE3, 0xD5, 0xE5, 0xE4, 0xF5, 0xF6, 0xDA, 0xDE, 0xEA, 0xEE, 0x60, 0x61, 0x68, 0x69, 0x63, 0x67} {
		s = append(s, ev("evex/int", 1, 1, op, -1, true, tFVM, 16, false))
	}
	for _, op := range []byte{0xD1, 0xD2, 0xD3, 0xE1, 0xE2, 0xF1, 0xF2, 0xF3} {
		s = append(s, ev("evex/shiftx", 1, 1, op, -1, true, tM128, 32, true))
	}
	for _, op := range []byte{0x74, 0x75, 0x76, 0x64, 0x65, 0x66} {
		sp := ev("evex/cmpeq", 1, 1, op, -1, true, tFV, 32, false)
		sp.KReg = true
		if op != 0x76 && op != 0x66 {
			sp.Tuple = tFVM
		}
		s = append(s, sp)
	}
	for pp := byte(1); pp < 4; pp++ {
		sp := ev("evex/shuf", 1, pp, 0x70, -1, false, tFV, 32, false)
		sp.Imm = true
		s = append(s, sp)
	}
	for _, g := range []struct {
		op  byte
		ext int
	}{{0x71, 2}, {0x71, 4}, {0x71, 6}, {0x72, 0}, {0x72, 1}, {0x72, 2}, {0x72, 4}, {0x72, 6}, {0x73, 2}, {0x73, 3},
		{0x73, 6}, {0x73, 7}, {0x71, 0}, {0x72, 3}, {0x73, 1}} {
		sp := ev("evex/shifti", 1, 1, g.op, -1, true, tFV, 32, true)
		sp.Ext, sp.Imm = g.ext, true
		s = append(s, sp)
	}
	// map 2 (66)
	for _, op := range []byte{0x00, 0x04, 0x0B, 0x1C, 0x1D, 0x38, 0x3A, 0x3C, 0x3E, 0x10, 0x11, 0x12, 0x8D, 0x75,
		0x7D, 0x54, 0xCF, 0x66, 0x26} {
		sp := ev("evex/int38", 2, 1, op, -1, op != 0x1C && op != 0x1D && op != 0x54, tFVM, 8, false)
		sp.KReg = op == 0x26
		s = append(s, sp)
	}
	for _, op := range []byte{0x1E, 0x1F, 0x28, 0x2B, 0x39, 0x3B, 0x3D, 0x3F, 0x40, 0x45, 0x46, 0x47, 0x14, 0x15,
		0x16, 0x36, 0x76, 0x77, 0x7E, 0x7F, 0x55, 0x64, 0x65, 0x27, 0x29, 0x37} {
		sp := ev("evex/int38", 2, 1, op, -1, op != 0x1E && op != 0x1F && op != 0x55, tFV, 32, true)
		sp.KReg = op == 0x27 || op == 0x29 || op == 0x37
		s = append(s, sp)
	}
	for _, op := range []byte{0x26, 0x27} {
		sp := ev("evex/testnm", 2, 2, op, -1, true, tFV, 32, true)
		sp.KReg = true
		if op == 0x26 {
			sp.Tuple = tFVM
		}
		s = append(s, sp)
	}
	for _, op := range []byte{0x62, 0x63, 0x89, 0x8B} {
		e := 32
		if op < 0x80 {
			e = 8
		}
		s = append(s, ev("evex/compress", 2, 1, op, -1, false, tT1S, e, true))
	}
	for _, op := range []byte{0x18, 0x19, 0x58, 0x59, 0x78, 0x79} {
		e := map[byte]int{0x18: 32, 0x19: 64, 0x58: 32, 0x59: 64, 0x78: 8, 0x79: 16}[op]
		s = append(s, ev("evex/bcast", 2, 1, op, -1, false, tT1S, e, false))
	}
	for _, op := range []byte{0x1A, 0x5A} {
		sp := ev("evex/bcastx", 2, 1, op, -1, false, tT4, 32, true)
		sp.Mod = 2
		s = append(s, sp)
	}
	for _, op := range []byte{0x1B, 0x5B} {
		sp := ev("evex/bcastx", 2, 1, op, -1, false, tT8, 32, true)
		sp.Mod = 2
		s = append(s, sp)
	}
	for _, op := range []byte{0x7A, 0x7B, 0x7C} {
		sp := ev("evex/bcastg", 2, 1, op, -1, false, tNone, 32, true)
		sp.Mod = 1
		s = append(s, sp)
	}
	for op := byte(0x20); op <= 0x25; op++ {
		s = append(s, ev("evex/pmovx", 2, 1, op, -1, false, tPMOV, 8, false))
		s = append(s, ev("evex/pmovx", 2, 1, op+0x10, -1, false, tPMOV, 8, false))
	}
	// map 3 (66)
	for _, op := range []byte{0x00, 0x01, 0x03, 0x0F, 0x25, 0x23, 0x43, 0x44, 0xCE, 0xCF, 0x1E, 0x1F, 0x3E, 0x3F} {
		tuple := tFV
		if op == 0x0F || op == 0x44 || op == 0x3E || op == 0x3F {
			tuple = tFVM
		}
		sp := ev("evex/imm3a", 3, 1, op, -1, op != 0x00 && op != 0x01, tuple, 32, true)
		sp.Imm = true
		sp.KReg = op == 0x1E || op == 0x1F || op == 0x3E || op == 0x3F
		s = append(s, sp)
	}
	for _, op := range []byte{0x18, 0x38, 0x19, 0x39} {
		sp := ev("evex/insext", 3, 1, op, -1, op == 0x18 || op == 0x38, tT4, 32, true)
		sp.Imm = true
		s = append(s, sp)
	}
	for _, op := range []byte{0x1A, 0x3A, 0x1B, 0x3B} {
		sp := ev("evex/insext", 3, 1, op, -1, op == 0x1A || op == 0x3A, tT8, 32, true)
		sp.Imm = true
		s = append(s, sp)
	}
	// VEX: opmask instructions
	vx := func(name string, mp, pp, op byte, nds bool, mod int) EvexSpec {
		return EvexSpec{Name: name, Map: mp, PP: pp, Op: op, Ext: -1, W: -1, NDS: nds, Mod: mod, Vex: true, Tuple: tNone}
	}
	for pp := byte(0); pp < 4; pp++ {
		for _, op := range []byte{0x90, 0x91, 0x92, 0x93, 0x44, 0x98, 0x99} {
			s = append(s, vx("vex/kmask", 1, pp, op, false, 0))
		}
		for _, op := range []byte{0x41, 0x42, 0x45, 0x46, 0x47, 0x4A, 0x4B} {
			s = append(s, vx("vex/klogic", 1, pp, op, true, 1))
		}
	}
	for op := byte(0x30); op <= 0x33; op++ {
		sp := vx("vex/kshift", 3, 1, op, false, 1)
		sp.Imm = true
		s = append(s, sp)
	}
	for _, op := range []byte{0x44, 0xCE, 0xCF} {
		sp := vx("vex/clmulgf", 3, 1, op, true, 0)
		sp.Imm = true
		s = append(s, sp)
	}
	s = append(s, vx("vex/clmulgf", 2, 1, 0xCF, true, 0))
	return s
}

// Evex512Specs are the targeted WP-G families.
var Evex512Specs = evexSpecs()

// encInfo is what the generator drew for an encoding (for steering the state).
type encInfo struct {
	evex     bool
	l        int // vector length in bits
	k        int // EVEX.aaa
	z, b     bool
	mem      bool
	base     int // -1: none (or RIP)
	index    int // -1: none
	scale    int
	disp     int64 // after disp8*N
	n        int   // operand bytes (whole operand, for straddling)
	elem     int   // masking/broadcast element width in bytes
	rip      bool
	regs     []int // vector registers mentioned (reg, vvvv, rm)
	kreg     int   // a mask register operand (VEX), -1
	gprRM    int   // a general register in r/m (VEX KMOV, EVEX broadcast), -1
	immShift bool
}

// Evex512Targeted produces one encoding of sp and the fields it drew.
func Evex512Targeted(r *rand.Rand, sp EvexSpec) ([]byte, encInfo) {
	inf := encInfo{base: -1, index: -1, kreg: -1, gprRM: -1}
	var out []byte
	if r.IntN(40) == 0 {
		out = append(out, []byte{0x66, 0xF2, 0xF3, 0x40, 0x48, 0x2E, 0x67}[r.IntN(7)])
	}
	w := sp.W
	if w < 0 || r.IntN(16) == 0 {
		w = r.IntN(2)
	}
	nds := sp.NDS || r.IntN(10) == 0
	modrm := byte(r.IntN(256))
	switch sp.Mod {
	case 1:
		modrm |= 0xC0
	case 2:
		if modrm>>6 == 3 {
			modrm &^= 0xC0
		}
	default:
		if r.IntN(2) == 0 {
			modrm |= 0xC0
		} else if modrm>>6 == 3 {
			modrm &^= 0xC0
		}
	}
	if sp.Ext >= 0 && r.IntN(12) != 0 {
		modrm = modrm&^0x38 | byte(sp.Ext)<<3
	}
	if sp.Vex {
		rr, xx, bb := 0, 0, 0
		if r.IntN(10) == 0 {
			rr = 1
		}
		if r.IntN(10) == 0 {
			bb = 1
		}
		if r.IntN(10) == 0 {
			xx = 1
		}
		vvvv := 0
		if nds {
			vvvv = r.IntN(8)
			if r.IntN(10) == 0 {
				vvvv = r.IntN(16)
			}
		}
		l := r.IntN(2)
		if sp.Name == "vex/klogic" && r.IntN(8) != 0 {
			l = 1
		} else if sp.Name != "vex/clmulgf" && r.IntN(8) != 0 {
			l = 0
		}
		mp, pp := sp.Map, sp.PP
		if r.IntN(40) == 0 {
			pp = byte(r.IntN(4))
		}
		if mp == 1 && xx == 0 && bb == 0 && w == 0 && r.IntN(2) == 0 {
			out = append(out, 0xC5, byte((1-rr)<<7|(^vvvv&15)<<3|l<<2)|pp)
		} else {
			out = append(out, 0xC4, byte((1-rr)<<7|(1-xx)<<6|(1-bb)<<5)|mp, byte(w<<7|(^vvvv&15)<<3|l<<2)|pp)
		}
		out = append(out, sp.Op)
		inf.l = 128 << l
	} else {
		rr, xx, bb, rr2 := r.IntN(2), r.IntN(2), r.IntN(2), r.IntN(2)
		if sp.KReg || sp.Ext >= 0 {
			if r.IntN(10) != 0 {
				rr, rr2 = 0, 0
			}
		}
		if sp.Mod == 1 && sp.Name == "evex/bcastg" && r.IntN(8) != 0 {
			xx = 0
		}
		vvvv := 0
		if nds {
			vvvv = r.IntN(32)
		} else if r.IntN(16) == 0 {
			vvvv = r.IntN(32)
		}
		ll := r.IntN(3)
		if r.IntN(24) == 0 {
			ll = 3
		}
		bbit := 0
		if (modrm>>6 != 3 && r.IntN(4) == 0) || r.IntN(14) == 0 {
			bbit = 1
		}
		k := 0
		if r.IntN(3) != 0 {
			k = 1 + r.IntN(7)
		}
		z := 0
		if (k != 0 && r.IntN(4) == 0) || r.IntN(24) == 0 {
			z = 1
		}
		if !nds && r.IntN(16) != 0 {
			vvvv = 0
		}
		mp, pp := sp.Map, sp.PP
		if r.IntN(48) == 0 {
			pp = byte(r.IntN(4))
		}
		if r.IntN(64) == 0 {
			mp = byte(r.IntN(8))
		}
		p0 := byte((1-rr)<<7|(1-xx)<<6|(1-bb)<<5|(1-rr2)<<4) | mp
		if r.IntN(64) == 0 {
			p0 |= 8
		}
		p1 := byte(w<<7|(^vvvv&15)<<3|4) | pp
		if r.IntN(64) == 0 {
			p1 &^= 4
		}
		p2 := byte(z<<7 | ll<<5 | bbit<<4 | (1-(vvvv>>4))<<3 | k)
		out = append(out, 0x62, p0, p1, p2, sp.Op)
		inf.evex, inf.l, inf.k, inf.z, inf.b = true, 128<<ll, k, z == 1, bbit == 1
		if ll == 3 {
			inf.l = 512
		}
		inf.regs = append(inf.regs, int(modrm>>3&7)+8*rr+16*rr2, vvvv)
		if modrm>>6 == 3 {
			inf.regs = append(inf.regs, int(modrm&7)+8*bb+16*xx)
		}
		e := sp.E
		if sp.EW && w == 1 {
			e = 64
		}
		inf.elem = e / 8
		switch sp.Tuple {
		case tFV:
			if inf.b {
				inf.n = e / 8
			} else {
				inf.n = inf.l / 8
			}
		case tFVM:
			inf.n = inf.l / 8
		case tT1S:
			inf.n = e / 8
		case tM128:
			inf.n = 16
		case tT4:
			inf.n = 16
		case tT8:
			inf.n = 32
		case tPMOV:
			inf.n = inf.l / 8 / 2
		}
		if inf.n == 0 {
			inf.n = 1
		}
		_ = bb
	}
	out = append(out, modrm)
	// SIB / displacement
	md, rm := int(modrm>>6), int(modrm&7)
	if md != 3 {
		inf.mem = true
		if rm == 4 {
			sib := byte(r.IntN(256))
			out = append(out, sib)
			inf.scale = 1 << (sib >> 6)
			if idx := int(sib >> 3 & 7); idx != 4 || !inf.evex {
				inf.index = idx // REX.X/EVEX.X ignored for steering: a wrong guess only leaves the address wild
			}
			if sib&7 == 5 && md == 0 {
				inf.base = -1
			} else {
				inf.base = int(sib & 7)
			}
		} else if rm == 5 && md == 0 {
			inf.rip = true
		} else {
			inf.base = rm
		}
		switch {
		case md == 1:
			d := []byte{0, 1, 2, 0xFF, 0xFE, 3, 4, 0x7F, 0x80, 8}[r.IntN(10)]
			if r.IntN(2) == 0 {
				d = byte(r.IntN(256))
			}
			out = append(out, d)
			inf.disp = int64(int8(d))
			if inf.evex {
				inf.disp *= int64(inf.n)
			}
		case md == 2 || (md == 0 && (rm == 5 || (rm == 4 && out[len(out)-1]&7 == 5))):
			d := uint32(r.Int32N(1 << 12))
			if r.IntN(3) == 0 {
				d = r.Uint32()
			}
			out = append(out, byte(d), byte(d>>8), byte(d>>16), byte(d>>24))
			inf.disp = int64(int32(d))
		}
	}
	if sp.Imm {
		imm := byte(r.IntN(256))
		if sp.ImmLimit > 0 && r.IntN(8) != 0 {
			imm = byte(r.IntN(sp.ImmLimit))
		}
		if r.IntN(3) == 0 {
			imm = []byte{0, 1, 2, 3, 0x11, 0x10, 0x01, 0x96, 0xE8, 0xFF, 0x80, 4, 7, 8, 15, 16, 31, 63, 64}[r.IntN(19)]
		}
		out = append(out, imm)
	}
	// random tail (never executed: the runner single-steps), so that a mis-decoded length shows
	for len(out) < 15 && r.IntN(3) != 0 {
		out = append(out, byte(r.IntN(256)))
	}
	if len(out) > 15 {
		out = out[:15]
	}
	return out, inf
}

// EvexSweep is a random EVEX encoding of map mp (0-7), prefix pp and opcode op: every field
// random (the decoder must reject everything outside the subset, and agree with hardware on
// the rest).
func EvexSweep(r *rand.Rand, mp, pp, op byte) []byte {
	p0 := byte(r.IntN(256))&^0x0F | mp&7
	if r.IntN(16) == 0 {
		p0 |= 8
	}
	p1 := byte(r.IntN(256))&^7 | 4 | pp
	if r.IntN(16) == 0 {
		p1 &^= 4
	}
	p2 := byte(r.IntN(256))
	out := []byte{0x62, p0, p1, p2, op}
	for len(out) < 15 {
		out = append(out, byte(r.IntN(256)))
		if r.IntN(3) == 0 && len(out) > 5 {
			out[len(out)-1] = []byte{0, 0xC0, 0xC8, 0x04, 0x44, 0x24, 0x10, 0x05}[r.IntN(8)]
		}
	}
	return out
}

// randZMMWords is one ZMM register value: element-class patterns.
func randZMMWords(r *rand.Rand) [8]uint64 {
	var v [8]uint64
	switch r.IntN(8) {
	case 0:
	case 1:
		for i := range v {
			v[i] = ^uint64(0)
		}
	case 2:
		// small byte values (indices, counts)
		for i := range v {
			for b := 0; b < 8; b++ {
				v[i] |= uint64(r.IntN(128)) << (8 * b)
			}
		}
	case 3:
		for i := range v {
			v[i] = RandValue(r)
		}
	case 4:
		// FP edge values per 32/64-bit lane
		w := []int{32, 64}[r.IntN(2)]
		for i := range v {
			if w == 64 {
				v[i] = FPEdge(r, 64)
			} else {
				v[i] = FPEdge(r, 32) | FPEdge(r, 32)<<32
			}
		}
	default:
		for i := range v {
			v[i] = r.Uint64()
		}
	}
	return v
}

// randMask is an opmask value: all ones, zero, low-n bits, sparse or random.
func randMask(r *rand.Rand) uint64 {
	switch r.IntN(8) {
	case 0:
		return ^uint64(0)
	case 1:
		return 0
	case 2:
		n := r.IntN(65)
		if n == 64 {
			return ^uint64(0)
		}
		return 1<<uint(n) - 1
	case 3:
		return 1 << uint(r.IntN(64))
	case 4:
		return uint64(r.IntN(256))
	default:
		return r.Uint64()
	}
}

func setZMM(s *State, n int, v [8]uint64) {
	switch {
	case n < 16:
		s.XMM[n] = [2]uint64{v[0], v[1]}
		s.YMMH[n] = [2]uint64{v[2], v[3]}
		s.ZMMH[n] = [4]uint64{v[4], v[5], v[6], v[7]}
	case n < 32:
		s.ZMMX[n-16] = v
	}
}

// Evex512Setup is a random initial state for an encoding drawn by Evex512Targeted.
func Evex512Setup(r *rand.Rand, b []byte, inf encInfo, fp bool) State {
	s := Setup(r, b) // GPRs, XMM/YMM, flags, FS base, seed (x86asm cannot steer EVEX)
	for i := 0; i < 32; i++ {
		if r.IntN(6) != 0 {
			setZMM(&s, i, randZMMWords(r))
		} else if i < 16 {
			s.ZMMH[i] = [4]uint64{r.Uint64(), r.Uint64(), r.Uint64(), r.Uint64()}
		}
	}
	for i := 0; i < 8; i++ {
		s.K[i] = randMask(r)
	}
	if fp {
		s.SetMXCSR(RandMXCSR(r))
	}
	if inf.gprRM >= 0 {
		s.Regs[inf.gprRM] = RandValue(r)
	}
	if !inf.mem || inf.rip {
		return s
	}
	n := inf.n
	if n == 0 {
		n = 64
	}
	// the operand mostly inside the buffer, sometimes aligned, sometimes straddling an end with
	// the elements outside the buffer masked off (fault suppression) or not
	var target uint64
	straddle := false
	switch k := r.IntN(20); {
	case k < 13:
		hi := L.DataSize - n
		if r.IntN(2) == 0 {
			target = L.DataBase + uint64(r.IntN(hi/n+1)*n)
		} else {
			target = L.DataBase + uint64(r.IntN(hi+1))
		}
	case k < 18:
		straddle = true
		if r.IntN(2) == 0 {
			target = L.DataBase + L.DataSize - uint64(r.IntN(n))
			target -= target % uint64(max(inf.elem, 1))
		} else {
			target = L.DataBase - uint64(1+r.IntN(n))
		}
	default:
		return s
	}
	if inf.base < 0 {
		return s
	}
	var idx uint64
	if inf.index >= 0 && inf.index != inf.base {
		idx = uint64(r.IntN(8))
		s.Regs[inf.index] = idx
		if inf.index == 4 {
			idx = s.Regs[4]
			if s.Regs[4] > target {
				return s
			}
		}
	} else if inf.index == inf.base {
		return s
	}
	s.Regs[inf.base] = target - idx*uint64(inf.scale) - uint64(inf.disp)
	if straddle && inf.evex && inf.k != 0 && inf.elem > 0 && r.IntN(3) != 0 {
		// select exactly the elements inside the buffer
		var m uint64
		cnt := inf.l / 8 / inf.elem
		for i := 0; i < cnt && i < 64; i++ {
			a := target + uint64(i*inf.elem)
			if a >= L.DataBase && a+uint64(inf.elem) <= L.DataBase+L.DataSize {
				m |= 1 << uint(i)
			}
		}
		if r.IntN(4) == 0 {
			m &= r.Uint64()
		}
		s.K[inf.k] = m
	}
	return s
}

// EvexClass names a case of spec sp.
func EvexClass(sp EvexSpec, b []byte) string {
	if sp.Vex {
		return fmt.Sprintf("%s/%d.%d.%02x", sp.Name, sp.Map, sp.PP, sp.Op)
	}
	return fmt.Sprintf("%s/%d.%d.%02x", sp.Name, sp.Map, sp.PP, sp.Op)
}

// IsEvexFP reports whether sp is a floating-point family (run under random MXCSR settings).
func IsEvexFP(sp EvexSpec) bool {
	return sp.Name == "evex/fpps" || sp.Name == "evex/fppd" || sp.Name == "evex/fpcmp"
}

// EvexInfo recovers the steering fields of a real (harvested) EVEX or VEX encoding: the vector
// length, mask, broadcast and memory operand, with disp8 scaled by the full vector (tuple FVM;
// the harvested Go instructions are full-vector forms).
func EvexInfo(b []byte) encInfo {
	inf := encInfo{base: -1, index: -1, kreg: -1, gprRM: -1}
	var i int
	switch {
	case len(b) >= 6 && b[0] == 0x62:
		p2 := b[3]
		inf.evex = true
		inf.k, inf.z, inf.b = int(p2&7), p2&0x80 != 0, p2&0x10 != 0
		inf.l = 128 << (p2 >> 5 & 3)
		if inf.l > 512 {
			inf.l = 512
		}
		inf.elem = 8
		inf.n = inf.l / 8
		if inf.b {
			inf.n = 8
		}
		i = 5
	case len(b) >= 4 && b[0] == 0xC5:
		i = 3
	case len(b) >= 5 && b[0] == 0xC4:
		i = 4
	default:
		return inf
	}
	if i >= len(b) {
		return inf
	}
	modrm := b[i]
	md, rm := int(modrm>>6), int(modrm&7)
	i++
	if md == 3 {
		return inf
	}
	inf.mem = true
	if rm == 4 && i < len(b) {
		sib := b[i]
		i++
		inf.scale = 1 << (sib >> 6)
		if idx := int(sib >> 3 & 7); idx != 4 {
			inf.index = idx
		}
		if sib&7 == 5 && md == 0 {
			inf.base = -1
			md = 2
		} else {
			inf.base = int(sib & 7)
		}
	} else if rm == 5 && md == 0 {
		inf.rip = true
		return inf
	} else {
		inf.base = rm
	}
	if md == 1 && i < len(b) {
		inf.disp = int64(int8(b[i]))
		if inf.evex {
			inf.disp *= int64(inf.n)
		}
	} else if md == 2 && i+4 <= len(b) {
		inf.disp = int64(int32(uint32(b[i]) | uint32(b[i+1])<<8 | uint32(b[i+2])<<16 | uint32(b[i+3])<<24))
	}
	if inf.n == 0 {
		inf.n = 8
	}
	return inf
}
