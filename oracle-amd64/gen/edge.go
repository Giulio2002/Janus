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
	}
	return out
}
