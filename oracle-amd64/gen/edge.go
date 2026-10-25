package gen

import (
	"math/rand/v2"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// EdgeCase is a hand-targeted encoding with a state chosen to hit a corner of its semantics.
type EdgeCase struct {
	Class string
	Bytes []byte
	State State
}

// rex returns a REX prefix byte (or nothing) for 64-bit width w and high register bits.
func rexFor(w int, r, x, b int, force bool) []byte {
	v := byte(0x40)
	if w == 64 {
		v |= 8
	}
	if r >= 8 {
		v |= 4
	}
	if x >= 8 {
		v |= 2
	}
	if b >= 8 {
		v |= 1
	}
	if v == 0x40 && !force {
		return nil
	}
	return []byte{v}
}

func cat(parts ...[]byte) []byte {
	var out []byte
	for _, p := range parts {
		out = append(out, p...)
	}
	return out
}

func modrmRR(reg, rm int) byte { return 0xC0 | byte(reg&7)<<3 | byte(rm&7) }

// sizePrefix gives the operand-size prefix and REX.W for width w (16/32/64).
func sizePrefix(w int) []byte {
	if w == 16 {
		return []byte{0x66}
	}
	return nil
}

func randReg(r *rand.Rand, noRSP bool) int {
	for {
		x := r.IntN(16)
		if !(noRSP && x == 4) {
			return x
		}
	}
}

// Edges produces n rounds of every edge family.
func Edges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	emit := func(class string, b []byte, s State) {
		if OK(b) {
			out = append(out, EdgeCase{"edge/" + class, b, s})
		}
	}
	widths := []int{16, 32, 64}
	for round := 0; round < n; round++ {
		// (a) BSF/BSR/TZCNT/LZCNT/POPCNT with zero (or low-zero) source
		for _, w := range widths {
			for _, op := range [][]byte{{0x0F, 0xBC}, {0x0F, 0xBD}, {0xF3, 0x0F, 0xBC}, {0xF3, 0x0F, 0xBD}, {0xF3, 0x0F, 0xB8}} {
				d, sreg := randReg(r, true), randReg(r, true)
				pre, opc := []byte(nil), op
				if op[0] == 0xF3 {
					pre, opc = []byte{0xF3}, op[1:]
				}
				b := cat(sizePrefix(w), pre, rexFor(w, d, 0, sreg, false), opc, []byte{modrmRR(d, sreg)})
				s := Setup(r, b)
				switch r.IntN(3) {
				case 0:
					s.Regs[sreg] = 0
				case 1:
					s.Regs[sreg] = r.Uint64() &^ (1<<uint(w) - 1) // low w bits zero
					if w == 64 {
						s.Regs[sreg] = 0
					}
				default:
					s.Regs[sreg] = 1 << uint(r.IntN(w))
				}
				emit("bitscan", b, s)
			}
		}
		// (b) CMOVcc 32/16/64-bit under every flag combination subset (false conditions included)
		for _, w := range widths {
			cc := r.IntN(16)
			d, sreg := randReg(r, true), randReg(r, true)
			b := cat(sizePrefix(w), rexFor(w, d, 0, sreg, false), []byte{0x0F, 0x40 + byte(cc), modrmRR(d, sreg)})
			for k := 0; k < 8; k++ {
				s := Setup(r, b)
				s.RFlags = FlagCombo(r.IntN(64))
				s.Regs[d] = r.Uint64()
				emit("cmov", b, s)
			}
		}
		// (c) MUL/IMUL/DIV/IDIV edge values
		for _, w := range []int{8, 16, 32, 64} {
			for ext := 4; ext < 8; ext++ {
				src := randReg(r, true)
				op := byte(0xF7)
				if w == 8 {
					op = 0xF6
					src = r.IntN(8) // includes AH..BH without REX
				}
				b := cat(sizePrefix(w), rexFor(w, 0, 0, src, false), []byte{op, modrmRR(ext, src)})
				s := Setup(r, b)
				mask := uint64(1)<<uint(w) - 1
				if w == 64 {
					mask = ^uint64(0)
				}
				min := uint64(1) << uint(w-1)
				dv := []uint64{0, 1, mask, mask - 1, min, min - 1, 2, 3, uint64(r.IntN(1000)), r.Uint64() & mask}[r.IntN(10)]
				setSrc := func(v uint64) {
					if w == 8 && src >= 4 && src < 8 {
						s.Regs[src-4] = s.Regs[src-4]&^0xff00 | (v&0xff)<<8
					} else {
						s.Regs[src] = s.Regs[src]&^mask | v&mask
					}
				}
				setSrc(dv)
				switch r.IntN(5) {
				case 0: // quotient exactly -2^(w-1): dividend = min * divisor (signed)
					if w < 64 {
						s.Regs[0] = s.Regs[0]&^mask | min&mask
						s.Regs[2] = s.Regs[2] &^ mask
						if w == 8 {
							s.Regs[0] = s.Regs[0]&^0xffff | uint64(0xff80)
						}
						setSrc(1)
					} else {
						s.Regs[0], s.Regs[2] = min, ^uint64(0)
						setSrc(1)
					}
				case 1: // -2^(w-1) / -1 overflow
					s.Regs[0] = s.Regs[0]&^mask | min&mask
					s.Regs[2] = s.Regs[2] | mask
					if w == 8 {
						s.Regs[0] = s.Regs[0]&^0xffff | 0xff80
					}
					setSrc(mask)
				case 2: // unsigned overflow: high half >= divisor
					s.Regs[2] = s.Regs[2]&^mask | (dv & mask)
				case 3:
					s.Regs[2] = s.Regs[2] &^ mask
				}
				emit("muldiv", b, s)
			}
			if w > 8 {
				// IMUL r, r/m ; r, r/m, imm8 ; r, r/m, imm32
				d, sreg := randReg(r, true), randReg(r, true)
				for _, form := range [][]byte{{0x0F, 0xAF, modrmRR(d, sreg)}, {0x6B, modrmRR(d, sreg), byte(r.IntN(256))},
					{0x69, modrmRR(d, sreg), byte(r.IntN(256)), byte(r.IntN(256)), 0x80, 0xff}} {
					if w == 16 && form[0] == 0x69 {
						form = form[:4]
					}
					b := cat(sizePrefix(w), rexFor(w, d, 0, sreg, false), form)
					s := Setup(r, b)
					s.Regs[sreg] = []uint64{1 << 63, 1<<31 + uint64(r.IntN(3)), 0x8000, 0xffffffff, ^uint64(0), r.Uint64()}[r.IntN(6)]
					emit("imul", b, s)
				}
			}
		}
		// (d) 8-bit operations on AH..BH (no REX) vs SPL..DIL (REX)
		for _, op := range []byte{0x00, 0x02, 0x08, 0x20, 0x28, 0x30, 0x38, 0x88, 0x8A, 0x84, 0x86} {
			reg, rm := r.IntN(8), r.IntN(8)
			b := []byte{op, modrmRR(reg, rm)}
			emit("byte-regs", b, Setup(r, b))
			b = []byte{0x40, op, modrmRR(reg, rm)}
			emit("byte-regs", b, Setup(r, b))
		}
		for _, op := range [][]byte{{0x0F, 0xB6}, {0x0F, 0xBE}} {
			reg, rm := r.IntN(8), r.IntN(8)
			for _, rx := range [][]byte{nil, {0x40}, {0x48}} {
				b := cat(rx, op, []byte{modrmRR(reg, rm)})
				emit("byte-regs", b, Setup(r, b))
			}
		}
		// (e) RIP-relative loads/stores/lea, mostly hitting the buffer (it is reachable with
		// disp32 from TestPC), sometimes the code page itself or far away
		for _, form := range [][]byte{{0x48, 0x8B}, {0x48, 0x89}, {0x8B}, {0x89}, {0x48, 0x8D}, {0x0F, 0xB6}, {0x48, 0x03}, {0x80}, {0x48, 0x81}, {0x0F, 0x10}, {0x0F, 0x11}} {
			reg := r.IntN(8)
			head := cat(form, []byte{byte(reg<<3) | 5})
			var imm []byte
			switch form[len(form)-1] {
			case 0x80:
				head[len(head)-1] = byte(r.IntN(8)<<3) | 5
				imm = []byte{byte(r.IntN(256))}
			case 0x81:
				head[len(head)-1] = byte(r.IntN(8)<<3) | 5
				imm = []byte{byte(r.IntN(256)), 0, 0, 0}
			}
			n := uint64(len(head) + 4 + len(imm))
			var target uint64
			switch r.IntN(6) {
			case 0:
				target = L.CodePage + uint64(r.IntN(L.PageSize))
			case 1:
				target = L.DataBase - uint64(r.IntN(8))
			default:
				target = L.DataBase + uint64(r.IntN(L.DataSize-16))
			}
			disp := uint32(target - (L.TestPC + n))
			b := cat(head, []byte{byte(disp), byte(disp >> 8), byte(disp >> 16), byte(disp >> 24)}, imm)
			emit("riprel", b, Setup(r, b))
		}
		// (f) aligned SSE moves / xorps with (mis)aligned memory
		for _, op := range [][]byte{{0x0F, 0x28}, {0x0F, 0x29}, {0x66, 0x0F, 0x6F}, {0x66, 0x0F, 0x7F}, {0x0F, 0x57}, {0x66, 0x0F, 0xEF},
			{0x0F, 0x10}, {0x0F, 0x11}, {0xF3, 0x0F, 0x6F}, {0xF3, 0x0F, 0x7F}, {0x66, 0x0F, 0x28}, {0x66, 0x0F, 0x57}} {
			x := r.IntN(16)
			base := randReg(r, true)
			if base&7 == 5 {
				base = 3
			}
			pre := []byte(nil)
			opc := op
			if op[0] != 0x0F {
				pre, opc = op[:1], op[1:]
			}
			b := cat(pre, rexFor(32, x, 0, base, false), opc, []byte{byte(x&7)<<3 | byte(base&7)})
			s := Setup(r, b)
			s.Regs[base] = L.DataBase + 16*uint64(r.IntN(255)) + []uint64{0, 0, 0, 1, 4, 8, 12, 15}[r.IntN(8)]
			emit("sse-align", b, s)
		}
		// (g) xchg mem, reg
		for _, w := range []int{8, 16, 32, 64} {
			reg, base := randReg(r, false), randReg(r, true)
			if base&7 == 5 {
				base = 6
			}
			op := byte(0x87)
			if w == 8 {
				op = 0x86
			}
			b := cat(sizePrefix(w), rexFor(w, reg, 0, base, false), []byte{op, byte(reg&7)<<3 | byte(base&7)})
			s := Setup(r, b)
			s.Regs[base] = L.DataBase + uint64(r.IntN(L.DataSize-8))
			emit("xchg-mem", b, s)
		}
		// (i) CMPXCHG / XADD on memory, locked or not, with the accumulator equal to the
		// memory operand half of the time; source or base aliasing RAX sometimes
		for _, w := range []int{8, 16, 32, 64} {
			for _, op := range []byte{0xB0, 0xC0} {
				reg, base := randReg(r, false), randReg(r, true)
				if base&7 == 5 {
					base = 6
				}
				if r.IntN(6) == 0 {
					reg = 0
				}
				if r.IntN(8) == 0 {
					base = 0
				}
				o := op
				if w > 8 {
					o++
				}
				var lock []byte
				if r.IntN(3) != 0 {
					lock = []byte{0xF0}
				}
				b := cat(lock, sizePrefix(w), rexFor(w, reg, 0, base, w == 8 && r.IntN(2) == 0), []byte{0x0F, o, byte(reg&7)<<3 | byte(base&7)})
				s := Setup(r, b)
				off := uint64(r.IntN(L.DataSize - 8))
				if r.IntN(10) == 0 {
					off = uint64(L.DataSize - 1 - r.IntN(4))
				}
				s.Regs[base] = L.DataBase + off
				if r.IntN(2) == 0 && off+uint64(w/8) <= L.DataSize {
					for k := 0; k < w/8; k++ {
						s.Init = append(s.Init, [2]int{int(off) + k, int(s.Regs[0] >> (8 * k) & 0xff)})
					}
				}
				emit("cmpxchg-xadd", b, s)
			}
		}
		// (j) CMPXCHG8B / CMPXCHG16B: aligned or not, equal half of the time
		for _, w := range []int{64, 128} {
			base := randReg(r, true)
			if base&7 == 5 || base == 0 || base == 1 || base == 2 || base == 3 {
				base = 6 + r.IntN(2)
			}
			var lock []byte
			if r.IntN(3) != 0 {
				lock = []byte{0xF0}
			}
			b := cat(lock, rexFor(w/2, 0, 0, base, false), []byte{0x0F, 0xC7, 1<<3 | byte(base&7)})
			s := Setup(r, b)
			off := 16 * uint64(r.IntN(L.DataSize/16-1))
			if r.IntN(4) == 0 {
				off += []uint64{1, 4, 8, 12}[r.IntN(4)]
			}
			s.Regs[base] = L.DataBase + off
			if r.IntN(2) == 0 {
				lo, hi := s.Regs[0], s.Regs[2]
				n := w / 16
				for k := 0; k < n; k++ {
					s.Init = append(s.Init, [2]int{int(off) + k, int(lo >> (8 * k) & 0xff)})
					s.Init = append(s.Init, [2]int{int(off) + n + k, int(hi >> (8 * k) & 0xff)})
				}
			}
			emit("cmpxchg-dbl", b, s)
		}
		// (k) MOVS / STOS with and without REP: small counts, overlapping and disjoint
		// buffers, runs that leave the buffer part-way
		for _, w := range []int{8, 16, 32, 64} {
			for _, op := range []byte{0xA4, 0xAA} {
				o := op
				if w > 8 {
					o++
				}
				var rp []byte
				if r.IntN(4) != 0 {
					rp = []byte{0xF3}
				}
				b := cat(rp, sizePrefix(w), rexFor(w, 0, 0, 0, false), []byte{o})
				s := Setup(r, b)
				s.Regs[1] = []uint64{0, 1, 2, 3, 5, 8, 13, 16, 31, 64, 200}[r.IntN(11)]
				src := uint64(r.IntN(L.DataSize))
				dst := uint64(r.IntN(L.DataSize))
				switch r.IntN(4) {
				case 0:
					dst = src + uint64(r.IntN(9))
				case 1:
					dst = src - uint64(r.IntN(9))
				}
				s.Regs[6], s.Regs[7] = L.DataBase+src, L.DataBase+dst
				// half of them with DF = 1 (backward)
				s.RFlags &^= L.FlagDF
				if r.IntN(2) == 0 {
					s.RFlags |= L.FlagDF
				}
				emit("string", b, s)
			}
		}
		// (l) LOCK on forms that do not accept it (#UD): CMP/TEST/MOV to memory, register
		// destinations
		for _, b := range [][]byte{{0xF0, 0x48, 0x39, 0x06}, {0xF0, 0x85, 0x06}, {0xF0, 0x89, 0x06}, {0xF0, 0x48, 0x01, 0xC6},
			{0xF0, 0x0F, 0xC1, 0xC6}, {0xF0, 0x0F, 0xB1, 0xC6}, {0xF0, 0x87, 0xC6}, {0xF0, 0x0F, 0xBA, 0x26, 3},
			{0xF0, 0xF3, 0x01, 0x06}, {0xF2, 0xF0, 0x01, 0x06}, {0xF0, 0xF0, 0x01, 0x06}, {0xF0, 0xA5}, {0xF0, 0x90}, {0xF0, 0x0F, 0xAE, 0xF0}} {
			s := Setup(r, b)
			s.Regs[6] = L.DataBase + uint64(r.IntN(L.DataSize-8))
			emit("lock-ud", b, s)
		}
		// (m) unaligned 128-bit loads and stores in Go's memmove/memclr forms
		// (MOVDQU X, disp(DI)(BX*1) and friends), straddling the buffer ends sometimes
		for _, op := range [][]byte{{0xF3, 0x0F, 0x6F}, {0xF3, 0x0F, 0x7F}, {0x0F, 0x10}, {0x0F, 0x11}} {
			x := r.IntN(16)
			pre, opc := []byte(nil), op
			if op[0] == 0xF3 {
				pre, opc = op[:1], op[1:]
			}
			disp := byte(0xF0 - 16*r.IntN(8))
			b := cat(pre, rexFor(32, x, 0, 0, false), opc, []byte{0x44 | byte(x&7)<<3, 0x1F, disp})
			s := Setup(r, b)
			n := uint64(r.IntN(300))
			s.Regs[3] = n
			s.Regs[7] = L.DataBase + uint64(r.IntN(L.DataSize)) - n + 0x80
			emit("sse-memmove", b, s)
		}
		// (n) the TLS slot: MOVQ FS:-8, R14 (and the store, and other registers/offsets) with
		// FS:-8 inside the buffer, at its ends, and outside it
		for _, b := range [][]byte{
			{0x64, 0x4C, 0x8B, 0x34, 0x25, 0xF8, 0xFF, 0xFF, 0xFF}, {0x64, 0x4C, 0x89, 0x34, 0x25, 0xF8, 0xFF, 0xFF, 0xFF},
			{0x64, 0x48, 0x8B, 0x04, 0x25, 0xF8, 0xFF, 0xFF, 0xFF}, {0x64, 0x48, 0x8B, 0x0C, 0x25, 0x00, 0x00, 0x00, 0x00},
			{0x64, 0x8B, 0x04, 0x25, 0xF0, 0xFF, 0xFF, 0xFF}, {0x64, 0x48, 0x8B, 0x00}, {0x64, 0x4C, 0x8B, 0x70, 0xF8},
			{0x64, 0x48, 0x39, 0x04, 0x25, 0xF8, 0xFF, 0xFF, 0xFF}, {0x64, 0x48, 0xC7, 0x04, 0x25, 0xF8, 0xFF, 0xFF, 0xFF, 1, 0, 0, 0},
			{0x64, 0x48, 0x8D, 0x04, 0x25, 0xF8, 0xFF, 0xFF, 0xFF}} {
			s := Setup(r, b)
			offs := []uint64{8, 9, 16, 64, 2048, L.DataSize - 1, L.DataSize, L.DataSize + 7, L.DataSize + 8, L.DataSize + 9, 0, 7, 4}
			s.FSBase = L.DataBase + offs[r.IntN(len(offs))]
			if r.IntN(8) == 0 {
				s.FSBase = []uint64{0, 8, 1 << 46, 1<<47 - 1}[r.IntN(4)]
			}
			s.Regs[0] = L.DataBase + uint64(r.IntN(L.DataSize-8))
			emit("tls", b, s)
		}
		// (o) byte compares and masks on nearly equal vectors: every register a copy of one
		// value with a few bytes changed, memory operands at copies of it
		for _, b := range [][]byte{
			{0x66, 0x0F, 0x74, 0xC1}, {0x66, 0x44, 0x0F, 0x74, 0xC7}, {0x66, 0x0F, 0xD7, 0xD0}, {0x66, 0x48, 0x0F, 0xD7, 0xD1},
			{0x66, 0x0F, 0xDB, 0xC2}, {0x66, 0x0F, 0xEB, 0xC2}, {0x66, 0x0F, 0x60, 0xC0}, {0x66, 0x0F, 0x70, 0xC0, 0x00}, {0x66, 0x0F, 0x70, 0xC8, 0x1B},
			{0xC5, 0xFD, 0x74, 0xE1}, {0xC5, 0xF9, 0x74, 0xE1}, {0xC5, 0xFD, 0xD7, 0xD6}, {0xC5, 0xF9, 0xD7, 0xD6}, {0xC5, 0xD5, 0xDB, 0xF4},
			{0xC4, 0xE2, 0x7D, 0x17, 0xDB}, {0xC4, 0xE2, 0x7D, 0x17, 0xD9}, {0xC4, 0xE2, 0x79, 0x17, 0xD9}, {0xC4, 0xE2, 0x7D, 0x78, 0xC8},
			{0xC4, 0xE2, 0x79, 0x78, 0xC8}, {0xC4, 0xE2, 0x7D, 0x78, 0x0E}, {0xC5, 0xFD, 0x74, 0x0E}, {0xC5, 0xF5, 0xEF, 0x06},
			{0xC5, 0xF8, 0x77}, {0xC5, 0xFE, 0x6F, 0xC1}, {0xC5, 0xFA, 0x6F, 0xC1}, {0xC5, 0xF9, 0xEF, 0xC0}} {
			s := Setup(r, b)
			base := [2]uint64{r.Uint64(), r.Uint64()}
			hi := [2]uint64{r.Uint64(), r.Uint64()}
			if r.IntN(3) == 0 {
				base, hi = [2]uint64{^uint64(0), ^uint64(0)}, [2]uint64{^uint64(0), ^uint64(0)}
			}
			for i := range s.XMM {
				s.XMM[i], s.YMMH[i] = base, hi
				for k := r.IntN(3); k > 0; k-- {
					j := r.IntN(32)
					v := &s.XMM[i]
					if j >= 16 {
						v, j = &s.YMMH[i], j-16
					}
					v[j/8] ^= uint64(1+r.IntN(255)) << (8 * (j % 8))
				}
			}
			s.Regs[6] = L.DataBase + 32*uint64(r.IntN(L.DataSize/32))
			emit("vec-cmp", b, s)
		}
		// (p) VMOVDQA / VMOVNTDQ / MOVDQA alignment at 16 and 32 bytes, VMOVDQU across the
		// buffer ends
		for _, b := range [][]byte{
			{0xC5, 0xFD, 0x6F, 0x06}, {0xC5, 0xF9, 0x6F, 0x06}, {0xC5, 0xFD, 0x7F, 0x06}, {0xC5, 0xFD, 0xE7, 0x06}, {0xC5, 0xF9, 0xE7, 0x06},
			{0xC5, 0xFE, 0x6F, 0x06}, {0xC5, 0xFE, 0x7F, 0x06}, {0xC5, 0xFA, 0x7F, 0x06}, {0x66, 0x0F, 0x6F, 0x06}, {0x66, 0x0F, 0x74, 0x06}} {
			s := Setup(r, b)
			offs := []uint64{0, 16, 32, 48, 8, 1, 31, L.DataSize - 32, L.DataSize - 16, L.DataSize - 31, L.DataSize - 17, ^uint64(15)}
			s.Regs[6] = L.DataBase + 32*uint64(r.IntN(L.DataSize/32-1)) + offs[r.IntN(len(offs))]
			emit("vec-align", b, s)
		}
		// (h) push/pop/call/ret/leave with RSP in the buffer, at and across its ends
		for _, b := range [][]byte{{0x50}, {0x41, 0x57}, {0x66, 0x50}, {0x58}, {0x41, 0x5C}, {0x66, 0x58}, {0x6A, 0x80}, {0x68, 1, 2, 3, 0x84},
			{0xFF, 0x30}, {0x8F, 0x00}, {0xE8, 0x10, 0, 0, 0}, {0xFF, 0xD0}, {0xC3}, {0xC2, 8, 0}, {0xC9}, {0x5C}, {0x54}} {
			s := Setup(r, b)
			offs := []uint64{0, 1, 4, 7, 8, 16, 2048, L.DataSize - 9, L.DataSize - 8, L.DataSize - 7, L.DataSize - 1, L.DataSize, L.DataSize + 8, ^uint64(7)}
			sp := L.DataBase + offs[r.IntN(len(offs))]
			s.Regs[4] = sp
			if b[0] == 0xC9 {
				s.Regs[5] = sp
			}
			if b[0] == 0xFF && b[1] == 0x30 || b[0] == 0x8F {
				s.Regs[0] = L.DataBase + uint64(r.IntN(L.DataSize-8))
			}
			if b[0] == 0xFF && b[1] == 0xD0 {
				s.Regs[0] = codeTarget(r)
			}
			if b[0] == 0xC3 || b[0] == 0xC2 || b[0] == 0xC9 {
				if sp >= L.DataBase && sp <= L.DataBase+L.DataSize-8 {
					v := codeTarget(r)
					s.Init = nil
					for k := 0; k < 8; k++ {
						s.Init = append(s.Init, [2]int{int(sp - L.DataBase + uint64(k)), int(v >> (8 * k) & 0xff)})
					}
				}
			}
			emit("stack", b, s)
		}
		// (q) ENDBR64 at a gcc function entry, exactly and with one extra prefix (66, REX,
		// a segment override, FS, a second F3 or F2, LOCK) before or after the F3
		emit("endbr", []byte{0xF3, 0x0F, 0x1E, 0xFA}, Setup(r, []byte{0xF3, 0x0F, 0x1E, 0xFA}))
		for _, x := range []byte{0x66, 0x40, 0x48, 0x41, 0x2E, 0x3E, 0x64, 0xF3, 0xF2, 0xF0} {
			for _, b := range [][]byte{{x, 0xF3, 0x0F, 0x1E, 0xFA}, {0xF3, x, 0x0F, 0x1E, 0xFA}} {
				emit("endbr", b, Setup(r, b))
			}
		}
		emit("endbr", []byte{0xF3, 0x0F, 0x1E, 0xFB}, Setup(r, []byte{0xF3, 0x0F, 0x1E, 0xFB}))
	}
	// WP-C: the exact forms of the traps, the environment reads and PUSHFQ/POPFQ. POPFQ pops a
	// random image from a stack slot inside the buffer: mostly only status flags and DF (plus the
	// ignored IF/IOPL/reserved bits), sometimes with TF, NT, AC or ID (the model refuses those)
	for round := 0; round < n; round++ {
		for _, b := range [][]byte{{0xCC}, {0xCD, 0x03}, {0x0F, 0x0B}, {0xF4}, {0x0F, 0xA2}, {0x0F, 0x31}, {0x9C}} {
			emit("sys", b, Setup(r, b))
		}
		s := Setup(r, []byte{0x9D})
		off := 1024 + 8*r.IntN(256)
		s.Regs[4] = L.DataBase + uint64(off)
		v := uint64(r.IntN(1<<12)) & 0xED5 // CF PF AF ZF SF DF OF
		v |= uint64(r.IntN(2)) << 9        // IF (ignored at CPL 3)
		if r.IntN(4) == 0 {
			v |= uint64(1) << []uint{8, 14, 18, 21, 12, 16, 3}[r.IntN(7)] // TF NT AC ID IOPL RF reserved
		}
		for i := 0; i < 8; i++ {
			s.Init = append(s.Init, [2]int{off + i, int(v >> (8 * i) & 0xFF)})
		}
		emit("sys", []byte{0x9D}, s)
	}
	return out
}
