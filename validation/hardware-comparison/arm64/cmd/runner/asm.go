//go:build arm64

package main

// A tiny AArch64 encoder for the fixed trampoline. Every encoding here is checked by
// `runner -dump-trampoline | aarch64-linux-gnu-objdump` (see scripts/oracle.sh selftest).

type asm struct {
	base  uint64
	words []uint32
	fix   []func()
}

func (a *asm) pc() uint64    { return a.base + uint64(len(a.words))*4 }
func (a *asm) emit(w uint32) { a.words = append(a.words, w) }

func (a *asm) adr(rd int, target uint64) {
	off := int64(target - a.pc())
	if off < -(1<<20) || off >= 1<<20 {
		panic("adr out of range")
	}
	u := uint32(off)
	a.emit(0x10000000 | (u&3)<<29 | ((u>>2)&0x7ffff)<<5 | uint32(rd))
}

func (a *asm) ldr(rt, rn, off int) {
	if off%8 != 0 || off < 0 || off >= 32768 {
		panic("ldr offset")
	}
	a.emit(0xF9400000 | uint32(off/8)<<10 | uint32(rn)<<5 | uint32(rt))
}

func (a *asm) ldrw(rt, rn, off int) {
	a.emit(0xB9400000 | uint32(off/4)<<10 | uint32(rn)<<5 | uint32(rt))
}

func (a *asm) str(rt, rn, off int) {
	if off%8 != 0 || off < 0 || off >= 32768 {
		panic("str offset")
	}
	a.emit(0xF9000000 | uint32(off/8)<<10 | uint32(rn)<<5 | uint32(rt))
}

// ldrPost: ldr xt, [xn], #8 ; strPost: str xt, [xn], #8
func (a *asm) ldrPost8(rt, rn int) { a.emit(0xF8400400 | 8<<12 | uint32(rn)<<5 | uint32(rt)) }
func (a *asm) strPost8(rt, rn int) { a.emit(0xF8000400 | 8<<12 | uint32(rn)<<5 | uint32(rt)) }

// addImm: add xd|sp, xn|sp, #imm
func (a *asm) addImm(rd, rn, imm int) {
	a.emit(0x91000000 | uint32(imm)<<10 | uint32(rn)<<5 | uint32(rd))
}

func (a *asm) subsImm(rd, rn, imm int) {
	a.emit(0xF1000000 | uint32(imm)<<10 | uint32(rn)<<5 | uint32(rd))
}

// ldrq: ldr qt, [xn, #off] (unsigned offset, multiple of 16)
func (a *asm) ldrq(rt, rn, off int) {
	if off%16 != 0 || off < 0 || off >= 65536 {
		panic("ldrq offset")
	}
	a.emit(0x3DC00000 | uint32(off/16)<<10 | uint32(rn)<<5 | uint32(rt))
}

// FPCR (op0=3 op1=3 CRn=4 CRm=4 op2=0) and FPSR (op2=1).
func (a *asm) mrsFPCR(rt int) { a.emit(0xD53B4400 | uint32(rt)) }
func (a *asm) msrFPCR(rt int) { a.emit(0xD51B4400 | uint32(rt)) }
func (a *asm) mrsFPSR(rt int) { a.emit(0xD53B4420 | uint32(rt)) }
func (a *asm) msrFPSR(rt int) { a.emit(0xD51B4420 | uint32(rt)) }

func (a *asm) mrsTPIDR(rt int) { a.emit(0xD53BD040 | uint32(rt)) }
func (a *asm) msrTPIDR(rt int) { a.emit(0xD51BD040 | uint32(rt)) }

func (a *asm) movz(rd int, imm uint16) { a.emit(0xD2800000 | uint32(imm)<<5 | uint32(rd)) }
func (a *asm) msrNZCV(rt int)          { a.emit(0xD51B4200 | uint32(rt)) }
func (a *asm) svc0()                   { a.emit(0xD4000001) }
func (a *asm) ret()                    { a.emit(0xD65F03C0) }

func (a *asm) b(target uint64) {
	off := int64(target - a.pc())
	if off < -(1<<27) || off >= 1<<27 {
		panic("b out of range")
	}
	a.emit(0x14000000 | (uint32(off>>2) & 0x3ffffff))
}

// label-based conditional branches (patched once the label is known)
type label struct{ addr uint64 }

func (a *asm) bcond(cond uint32, l *label) {
	i := len(a.words)
	pc := a.pc()
	a.emit(0)
	a.fix = append(a.fix, func() {
		off := int64(l.addr - pc)
		a.words[i] = 0x54000000 | (uint32(off>>2)&0x7ffff)<<5 | cond
	})
}

func (a *asm) cbz(rt int, l *label) {
	i := len(a.words)
	pc := a.pc()
	a.emit(0)
	a.fix = append(a.fix, func() {
		off := int64(l.addr - pc)
		a.words[i] = 0xB4000000 | (uint32(off>>2)&0x7ffff)<<5 | uint32(rt)
	})
}

func (a *asm) bind(l *label) { l.addr = a.pc() }

func (a *asm) finish() []uint32 {
	for _, f := range a.fix {
		f()
	}
	return a.words
}
