package gen

import (
	"math/rand/v2"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// SSE packed integer and floating point on XMM (WP-D): SSE2, SSE3, SSSE3, SSE4.1 and SSE4.2
// (legacy encodings), Janus/Amd64/{InstrSSE,DecodeSSE,ExecSSE}.lean.

// SSEIntClasses are the packed-integer, move, shuffle, insert/extract and string classes
// (x86asm mnemonics, lower case) of WP-D.
var SSEIntClasses = strings.Fields(`paddb paddw paddd paddq psubb psubw psubd psubq paddsb paddsw
	paddusb paddusw psubsb psubsw psubusb psubusw pmullw pmulhw pmulhuw pmuludq pmaddwd
	pcmpeqw pcmpeqd pcmpgtb pcmpgtw pcmpgtd pandn punpcklwd punpckldq punpcklqdq punpckhbw
	punpckhwd punpckhdq punpckhqdq packsswb packssdw packuswb pminub pmaxub pminsw pmaxsw psadbw
	pavgb pavgw psllw pslld psllq psrlw psrld psrlq psraw psrad pslldq psrldq pshufhw pinsrw
	pextrw unpcklps unpckhps unpcklpd unpckhpd shufps shufpd movlhps movhlps movlps movhps
	movlpd movhpd movmskps movmskpd movntdq movntps movntpd movnti lddqu movddup movsldup
	movshdup phaddw phaddd phaddsw phsubw phsubd phsubsw pmaddubsw pmulhrsw psignw psignd
	pabsb pabsw pabsd palignr pblendvb blendvps blendvpd ptest pmovsxbw pmovsxbd pmovsxbq
	pmovsxwd pmovsxwq pmovsxdq pmovzxbw pmovzxbd pmovzxbq pmovzxwd pmovzxwq pmovzxdq pmuldq
	pcmpeqq movntdqa packusdw pcmpgtq pminsb pminsd pminuw pminud pmaxsb pmaxsd pmaxuw pmaxud
	pmulld phminposuw blendps blendpd pblendw pextrb pextrd pextrq extractps pinsrb insertps
	pinsrd pinsrq mpsadbw pcmpestrm pcmpestri pcmpistrm pcmpistri crc32`)

// SSEFPClasses are the packed floating-point classes of WP-D, with their lane width.
var SSEFPClasses = map[string]int{
	"addps": 32, "subps": 32, "mulps": 32, "divps": 32, "minps": 32, "maxps": 32, "sqrtps": 32,
	"addpd": 64, "subpd": 64, "mulpd": 64, "divpd": 64, "minpd": 64, "maxpd": 64, "sqrtpd": 64,
	"cmpps": 32, "cmppd": 64, "roundps": 32, "roundpd": 64, "haddps": 32, "hsubps": 32,
	"haddpd": 64, "hsubpd": 64, "addsubps": 32, "addsubpd": 64, "cvtdq2ps": 32, "cvtps2dq": 32,
	"cvttps2dq": 32, "cvtdq2pd": 64, "cvtpd2dq": 64, "cvttpd2dq": 64, "cvtps2pd": 32, "cvtpd2ps": 64,
}

// SSEIntSource are the conversions whose source lanes are integers.
var sseIntSource = map[string]bool{"cvtdq2ps": true, "cvtdq2pd": true}

func init() {
	for _, m := range SSEIntClasses {
		Modeled[m] = true
	}
	for m, w := range SSEFPClasses {
		Modeled[m] = true
		fpClasses[m] = fpInfo{width: w, packed: true}
	}
}

// SSERegexp matches every WP-D class (for `harvest -only`).
func SSERegexp() string {
	var all []string
	all = append(all, SSEIntClasses...)
	for m := range SSEFPClasses {
		all = append(all, m)
	}
	return "^(" + strings.Join(all, "|") + ")$"
}

func sseSpecs() []Spec {
	var s []Spec
	add := func(name string, pre []byte, op []byte, reg, mod int) {
		s = append(s, Spec{Name: name, Pre: pre, Op: op, Reg: reg, Mod3: mod})
	}
	b := func(x ...byte) []byte { return x }
	p66, pF3, pF2 := b(0x66), b(0xF3), b(0xF2)
	// 66 0F xx packed integer (and the MMX forms without 66, rejected)
	ints := []byte{0x14, 0x15, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D,
		0x75, 0x76, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD8, 0xD9, 0xDA, 0xDC, 0xDD, 0xDE, 0xDF, 0xE0, 0xE1,
		0xE2, 0xE3, 0xE4, 0xE5, 0xE8, 0xE9, 0xEA, 0xEC, 0xED, 0xEE, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,
		0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE}
	for _, o := range ints {
		for _, mod := range []int{1, 1, 2, 0} {
			add("sse/int", p66, b(0x0F, o), -1, mod)
		}
		add("sse/int-other", nil, b(0x0F, o), -1, 0)
		add("sse/int-other", pF3, b(0x0F, o), -1, 0)
	}
	// shift groups 66 0F 71/72/73 /r ib (register forms; every /r, memory forms rejected)
	for _, o := range []byte{0x71, 0x72, 0x73} {
		for r := 0; r < 8; r++ {
			add("sse/shift", p66, b(0x0F, o), r, 1)
		}
		add("sse/shift", p66, b(0x0F, o), -1, 0)
		add("sse/shift-other", nil, b(0x0F, o), -1, 1)
	}
	// moves: MOVLPS/MOVHLPS (12), MOVLPS m (13), MOVHPS/MOVLHPS (16), MOVHPS m (17), with 66
	// (MOVLPD/MOVHPD), F3 (MOVSLDUP/MOVSHDUP), F2 (MOVDDUP)
	for _, o := range []byte{0x12, 0x13, 0x16, 0x17} {
		for _, mod := range []int{1, 2, 0} {
			add("sse/mov", nil, b(0x0F, o), -1, mod)
			add("sse/mov", p66, b(0x0F, o), -1, mod)
			add("sse/mov", pF3, b(0x0F, o), -1, mod)
			add("sse/mov", pF2, b(0x0F, o), -1, mod)
		}
	}
	for _, mod := range []int{1, 2, 0} {
		add("sse/mov", nil, b(0x0F, 0x2B), -1, mod)       // MOVNTPS
		add("sse/mov", p66, b(0x0F, 0x2B), -1, mod)       // MOVNTPD
		add("sse/mov", p66, b(0x0F, 0xE7), -1, mod)       // MOVNTDQ
		add("sse/mov", pF2, b(0x0F, 0xF0), -1, mod)       // LDDQU
		add("sse/mov", nil, b(0x0F, 0xC3), -1, mod)       // MOVNTI
		add("sse/mov", p66, b(0x0F, 0x38, 0x2A), -1, mod) // MOVNTDQA
		add("sse/mov", nil, b(0x0F, 0x50), -1, mod)       // MOVMSKPS
		add("sse/mov", p66, b(0x0F, 0x50), -1, mod)       // MOVMSKPD
	}
	add("sse/mov-other", pF3, b(0x0F, 0xE7), -1, 0)
	add("sse/mov-other", nil, b(0x0F, 0xF0), -1, 0)
	add("sse/mov-other", p66, b(0x0F, 0xF7), -1, 1) // MASKMOVDQU (not modelled)
	// shuffles and unpacks (FP domain), PSHUFHW, PINSRW, PEXTRW
	for _, mod := range []int{1, 1, 2, 0} {
		add("sse/shuf", nil, b(0x0F, 0xC6), -1, mod)
		add("sse/shuf", p66, b(0x0F, 0xC6), -1, mod)
		add("sse/shuf", nil, b(0x0F, 0x14), -1, mod)
		add("sse/shuf", nil, b(0x0F, 0x15), -1, mod)
		add("sse/shuf", pF3, b(0x0F, 0x70), -1, mod)
		add("sse/ins", p66, b(0x0F, 0xC4), -1, mod)
		add("sse/ins", p66, b(0x0F, 0xC5), -1, mod)
	}
	add("sse/shuf-other", pF2, b(0x0F, 0xC6), -1, 0)
	// 66 0F 38 xx (SSSE3, SSE4.1, SSE4.2 PCMPGTQ) and the MMX / F3 neighbours
	o38 := []byte{0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x09, 0x0A, 0x0B, 0x10, 0x14, 0x15, 0x17, 0x1C,
		0x1D, 0x1E, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x28, 0x29, 0x2B, 0x30, 0x31, 0x32, 0x33, 0x34,
		0x35, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x41}
	for _, o := range o38 {
		for _, mod := range []int{1, 1, 2, 0} {
			add("sse/38", p66, b(0x0F, 0x38, o), -1, mod)
		}
		add("sse/38-other", nil, b(0x0F, 0x38, o), -1, 0)
		add("sse/38-other", pF3, b(0x0F, 0x38, o), -1, 0)
	}
	for _, o := range []byte{0x11, 0x12, 0x13, 0x16, 0x18, 0x19, 0x1A, 0x1F, 0x26, 0x27, 0x2C, 0x2D, 0x36, 0x42, 0xDB, 0xDC, 0xCF} {
		add("sse/38-other", p66, b(0x0F, 0x38, o), -1, 0)
	}
	// CRC32 (F2 0F 38 F0 / F1, 66 F2 = 16 bits, REX.W = 64)
	for _, mod := range []int{1, 1, 2, 0} {
		add("sse/crc32", pF2, b(0x0F, 0x38, 0xF0), -1, mod)
		add("sse/crc32", pF2, b(0x0F, 0x38, 0xF1), -1, mod)
		add("sse/crc32", b(0x66, 0xF2), b(0x0F, 0x38, 0xF1), -1, mod)
		add("sse/crc32", b(0xF2, 0x66), b(0x0F, 0x38, 0xF1), -1, mod)
	}
	add("sse/crc32-other", b(0x66, 0xF2), b(0x0F, 0x38, 0xF0), -1, 0)
	add("sse/crc32-other", b(0xF3), b(0x0F, 0x38, 0xF1), -1, 0)
	// 66 0F 3A xx ib (SSSE3 PALIGNR, SSE4.1, SSE4.2 string compares)
	o3a := []byte{0x08, 0x09, 0x0C, 0x0D, 0x0E, 0x0F, 0x14, 0x15, 0x16, 0x17, 0x20, 0x21, 0x22, 0x42, 0x60, 0x61, 0x62, 0x63}
	for _, o := range o3a {
		for _, mod := range []int{1, 1, 2, 0} {
			add("sse/3a", p66, b(0x0F, 0x3A, o), -1, mod)
		}
		add("sse/3a-other", nil, b(0x0F, 0x3A, o), -1, 0)
	}
	for _, o := range []byte{0x40, 0x41, 0x44, 0x0A, 0x0B, 0xDF, 0xCC} {
		add("sse/3a-other", p66, b(0x0F, 0x3A, o), -1, 0)
	}
	// packed floating point: arithmetic (none = PS, 66 = PD), CMPPS/PD, conversions, SSE3
	for _, o := range []byte{0x51, 0x58, 0x59, 0x5C, 0x5D, 0x5E, 0x5F, 0xC2, 0x5A, 0x5B} {
		for _, mod := range []int{1, 1, 2, 0} {
			add("sse/fp", nil, b(0x0F, o), -1, mod)
			add("sse/fp", p66, b(0x0F, o), -1, mod)
		}
	}
	for _, mod := range []int{1, 1, 2, 0} {
		add("sse/fp", pF3, b(0x0F, 0x5B), -1, mod) // CVTTPS2DQ
		add("sse/fp", p66, b(0x0F, 0xE6), -1, mod) // CVTTPD2DQ
		add("sse/fp", pF3, b(0x0F, 0xE6), -1, mod) // CVTDQ2PD
		add("sse/fp", pF2, b(0x0F, 0xE6), -1, mod) // CVTPD2DQ
		add("sse/fp", p66, b(0x0F, 0x7C), -1, mod) // HADDPD
		add("sse/fp", pF2, b(0x0F, 0x7C), -1, mod) // HADDPS
		add("sse/fp", p66, b(0x0F, 0x7D), -1, mod) // HSUBPD
		add("sse/fp", pF2, b(0x0F, 0x7D), -1, mod) // HSUBPS
		add("sse/fp", p66, b(0x0F, 0xD0), -1, mod) // ADDSUBPD
		add("sse/fp", pF2, b(0x0F, 0xD0), -1, mod) // ADDSUBPS
	}
	add("sse/fp-other", nil, b(0x0F, 0x52), -1, 0) // RSQRTPS (not modelled)
	add("sse/fp-other", nil, b(0x0F, 0x53), -1, 0) // RCPPS (not modelled)
	add("sse/fp-other", nil, b(0x0F, 0xE6), -1, 0)
	add("sse/fp-other", nil, b(0x0F, 0x7C), -1, 0)
	add("sse/fp-other", pF3, b(0x0F, 0xD0), -1, 0)
	return s
}

// SSESpecs are the legacy-encoded WP-D targets (also part of Specs).
var SSESpecs = sseSpecs()

func init() { Specs = append(Specs, SSESpecs...) }

// laneEdges are interesting element values (low bits taken per width).
var laneEdges = []uint64{0, 1, 2, 0x7F, 0x80, 0x81, 0xFF, 0xFE, 0x7FFF, 0x8000, 0x8001, 0xFFFF,
	0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFF, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
	0xFFFFFFFFFFFFFFFF, 0x00FF, 0xFF00, 0x0101, 0x4000, 0xC000, 15, 16, 31, 32, 63, 64}

// laneXMM is an XMM value with element width e: edge elements, small elements, random.
func laneXMM(r *rand.Rand, e int) [2]uint64 {
	var x [2]uint64
	switch r.IntN(6) {
	case 0:
		return [2]uint64{r.Uint64(), r.Uint64()}
	case 1:
		if r.IntN(2) == 0 {
			return [2]uint64{}
		}
		return [2]uint64{^uint64(0), ^uint64(0)}
	}
	n := 128 / e
	mask := uint64(1)<<uint(e) - 1
	if e == 64 {
		mask = ^uint64(0)
	}
	for i := 0; i < n; i++ {
		var v uint64
		switch r.IntN(4) {
		case 0, 1:
			v = laneEdges[r.IntN(len(laneEdges))]
		case 2:
			v = uint64(int64(r.IntN(33) - 16))
		default:
			v = r.Uint64()
		}
		v &= mask
		bit := i * e
		x[bit/64] |= v << uint(bit%64)
	}
	return x
}

// strXMM is a string operand for the SSE4.2 compares: elements from a small alphabet (so that
// matches, ranges and substrings occur), sometimes with a null element.
func strXMM(r *rand.Rand, words bool) [2]uint64 {
	var x [2]uint64
	n, e := 16, 8
	if words {
		n, e = 8, 16
	}
	alpha := []uint64{'a', 'b', 'c', 'd', 0x41, 0x7F, 0x80, 0xFF, 0xFFFF, 0x8000}
	k := 2 + r.IntN(len(alpha)-1)
	for i := 0; i < n; i++ {
		v := alpha[r.IntN(k)]
		if r.IntN(12) == 0 {
			v = 0
		}
		if r.IntN(16) == 0 {
			v = r.Uint64()
		}
		v &= uint64(1)<<uint(e) - 1
		bit := i * e
		x[bit/64] |= v << uint(bit%64)
	}
	if r.IntN(5) == 0 {
		// a needle copied from the haystack is set by the caller; here: a null at a random place
		i := r.IntN(n)
		bit := i * e
		x[bit/64] &^= (uint64(1)<<uint(e) - 1) << uint(bit%64)
	}
	return x
}

// strLen is an explicit length for PCMPESTRx: mostly small (also negative), sometimes a
// boundary or random value.
func strLen(r *rand.Rand) uint64 {
	switch r.IntN(8) {
	case 0:
		return []uint64{0x80000000, 0x7FFFFFFF, 0xFFFFFFF0, 0x100000005, 0x8000000000000000, 0xFFFFFFFFFFFFFFF8, 17, 16, 8, 9}[r.IntN(10)]
	case 1:
		return r.Uint64()
	}
	return uint64(int64(r.IntN(41) - 20))
}

// shr128 is x >> sh (sh < 64) as a 128-bit value.
func shr128(x [2]uint64, sh uint) [2]uint64 {
	if sh == 0 {
		return x
	}
	return [2]uint64{x[0]>>sh | x[1]<<(64-sh), x[1] >> sh}
}

func xmmArg(a x86asm.Arg) int {
	if g, ok := a.(x86asm.Reg); ok && g >= x86asm.X0 && g <= x86asm.X15 {
		return int(g - x86asm.X0)
	}
	return -1
}

// sseElem is the element width the class's lanes are steered at.
func sseElem(cls string) int {
	switch {
	case strings.HasSuffix(cls, "b") || strings.HasSuffix(cls, "bw") || cls == "psadbw" || cls == "mpsadbw" ||
		cls == "palignr" || cls == "pmaddubsw" || cls == "packsswb" || cls == "packuswb":
		return 8
	case strings.HasSuffix(cls, "w") || strings.HasSuffix(cls, "wd") || cls == "pmulhrsw":
		return 16
	case strings.HasSuffix(cls, "q") || strings.HasSuffix(cls, "qdq") || strings.HasSuffix(cls, "pd"):
		return 64
	}
	return 32
}

// setupSSE steers the operands of the WP-D classes: element edge values in the XMM registers
// and the memory operand, mostly-aligned 16-byte memory operands, shift counts, XMM0 blend
// masks, string operands and explicit lengths, integer lanes for CVTDQ2PS/PD.
func setupSSE(r *rand.Rand, s *State, inst x86asm.Inst, cls string) {
	_, isFP := SSEFPClasses[cls]
	if !Modeled[cls] || (!isFP && !inSSEInt(cls)) {
		return
	}
	str := strings.HasPrefix(cls, "pcmpestr") || strings.HasPrefix(cls, "pcmpistr")
	words := false
	if str {
		// imm8<0>: word elements
		if len(inst.Args) > 2 {
			if im, ok := inst.Args[2].(x86asm.Imm); ok {
				words = im&1 == 1
			}
		}
	}
	if !isFP {
		e := sseElem(cls)
		for i := range s.XMM {
			if r.IntN(3) != 0 {
				if str {
					s.XMM[i] = strXMM(r, words)
				} else {
					s.XMM[i] = laneXMM(r, e)
				}
			}
		}
	}
	if sseIntSource[cls] {
		for i := range s.XMM {
			for l := 0; l < 4; l++ {
				fpLane(&s.XMM[i], 32, l, FPInt(r)&0xFFFFFFFF)
			}
		}
	}
	// operand relations: equal elements for compares, a needle copied from the haystack
	if len(inst.Args) > 1 {
		d, src := xmmArg(inst.Args[0]), xmmArg(inst.Args[1])
		if d >= 0 && src >= 0 && d != src && r.IntN(4) == 0 {
			if str {
				// needle = a slice of the haystack
				s.XMM[d] = shr128(s.XMM[src], uint(8*r.IntN(8)))
			} else if !isFP {
				s.XMM[src] = s.XMM[d]
				s.XMM[src][r.IntN(2)] ^= uint64(r.IntN(2)) << uint(r.IntN(64))
			}
		}
	}
	switch {
	case str:
		s.Regs[0], s.Regs[2] = strLen(r), strLen(r)
	case cls == "pblendvb" || cls == "blendvps" || cls == "blendvpd":
		if r.IntN(2) == 0 {
			s.XMM[0] = laneXMM(r, map[string]int{"pblendvb": 8, "blendvps": 32, "blendvpd": 64}[cls])
		}
	case cls == "crc32":
		if r.IntN(4) == 0 {
			if g, ok := inst.Args[0].(x86asm.Reg); ok {
				if n, _, ok := regNum(g); ok && n != 4 {
					s.Regs[n] = []uint64{0, 0xFFFFFFFF, 0xFFFFFFFF00000000, 1}[r.IntN(4)]
				}
			}
		}
	case cls == "psllw" || cls == "pslld" || cls == "psllq" || cls == "psrlw" || cls == "psrld" ||
		cls == "psrlq" || cls == "psraw" || cls == "psrad":
		// the xmm-count forms: the count is the low quadword of the source
		if len(inst.Args) > 1 {
			c := []uint64{0, 1, 2, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255, 1 << 32, 1 << 63}[r.IntN(17)]
			hi := []uint64{0, 0, r.Uint64(), 1}[r.IntN(4)]
			if x := xmmArg(inst.Args[1]); x >= 0 {
				s.XMM[x] = [2]uint64{c, hi}
			} else if m, ok := inst.Args[1].(x86asm.Mem); ok {
				if ea, ok := effAddr(s, inst, m); ok {
					plantLE(s, ea, [2]uint64{c, hi}, 16)
				}
			}
		}
	}
	// memory operand: mostly 16-byte aligned (legacy SSE faults otherwise), element edge values
	for _, a := range inst.Args {
		m, ok := a.(x86asm.Mem)
		if !ok {
			continue
		}
		if inst.MemBytes == 16 && r.IntN(4) != 0 {
			if ea, ok := effAddr(s, inst, m); ok && ea >= L.DataBase && ea < L.DataBase+L.DataSize {
				if bn, _, bok := regNum(m.Base); bok && bn != 4 {
					s.Regs[bn] -= ea & 15
				}
			}
		}
		if ea, ok := effAddr(s, inst, m); ok && !isFP && r.IntN(2) == 0 {
			v := laneXMM(r, sseElem(cls))
			if str {
				v = strXMM(r, words)
			}
			n := inst.MemBytes
			if n <= 0 || n > 16 {
				n = 16
			}
			plantLE(s, ea, v, n)
		}
	}
}

var sseIntSet = map[string]bool{}

func init() {
	for _, m := range SSEIntClasses {
		sseIntSet[m] = true
	}
}

func inSSEInt(cls string) bool { return sseIntSet[cls] }

// legacy encodes [pre] [REX] op modrm [imm] for register operands reg, rm.
func legacyRR(pre []byte, op []byte, w64 bool, reg, rm int, imm ...byte) []byte {
	var out []byte
	out = append(out, pre...)
	out = append(out, rexFor(map[bool]int{true: 64, false: 32}[w64], reg, 0, rm, false)...)
	out = append(out, op...)
	out = append(out, modrmRR(reg, rm))
	return append(out, imm...)
}

func baseState(r *rand.Rand) State {
	var s State
	for i := range s.Regs {
		s.Regs[i] = RandValue(r)
	}
	s.Regs[4] = L.DataBase + 1024 + 8*uint64(r.IntN(256))
	s.RFlags = RandFlags(r)
	s.Seed = uint64(r.IntN(1 << 20))
	if r.IntN(4) != 0 {
		for i := range s.YMMH {
			s.YMMH[i] = [2]uint64{r.Uint64(), r.Uint64()}
		}
	}
	return s
}

// SSEEdges are the systematic WP-D families, per round: every PCMPESTRI/PCMPESTRM/PCMPISTRI/
// PCMPISTRM imm8 (all 128 over 128 rounds, both REX.W) on crafted strings and lengths; every
// shift by immediate at the counts around the element width; the saturating, packing,
// averaging and min/max operations on boundary elements; the packed floating-point operations
// on IEEE edge values in every lane under the 16 RC x FTZ/DAZ settings and each exception
// unmasked alone; CRC32 at every width.
func SSEEdges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	emit := func(class string, b []byte, s State) {
		if OK(b) {
			out = append(out, EdgeCase{"edge/" + class, b, s})
		}
	}
	p66 := []byte{0x66}
	for round := 0; round < n; round++ {
		// string compares
		for _, o := range []byte{0x60, 0x61, 0x62, 0x63} {
			imm := byte(round % 128)
			if r.IntN(3) == 0 {
				imm = byte(r.IntN(128))
			}
			d, sr := r.IntN(16), r.IntN(16)
			b := legacyRR(p66, []byte{0x0F, 0x3A, o}, r.IntN(4) == 0, d, sr, imm)
			s := baseState(r)
			for i := range s.XMM {
				s.XMM[i] = strXMM(r, imm&1 == 1)
			}
			if r.IntN(3) == 0 && d != sr {
				s.XMM[d] = shr128(s.XMM[sr], uint(8*r.IntN(8)))
			}
			s.Regs[0], s.Regs[2] = strLen(r), strLen(r)
			emit("pcmpstr", b, s)
		}
		// shifts by immediate: counts around the element width
		for _, o := range []byte{0x71, 0x72, 0x73} {
			for _, ext := range []int{2, 3, 4, 6, 7} {
				cnt := []byte{0, 1, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255}[r.IntN(16)]
				rm := r.IntN(16)
				b := cat(p66, rexFor(32, 0, 0, rm, false), []byte{0x0F, o, 0xC0 | byte(ext)<<3 | byte(rm&7), cnt})
				s := baseState(r)
				for i := range s.XMM {
					s.XMM[i] = laneXMM(r, 16)
				}
				emit("pshift", b, s)
			}
		}
		// saturating / packing / averaging / min-max / multiply-high on boundary elements
		for _, o := range []byte{0x63, 0x67, 0x6B, 0xD8, 0xD9, 0xDC, 0xDD, 0xE8, 0xE9, 0xEC, 0xED, 0xE0, 0xE3,
			0xE4, 0xE5, 0xF5, 0xF6, 0xDA, 0xDE, 0xEA, 0xEE, 0xD5, 0xF4} {
			d, sr := r.IntN(16), r.IntN(16)
			b := legacyRR(p66, []byte{0x0F, o}, false, d, sr)
			s := baseState(r)
			e := []int{8, 16, 32}[r.IntN(3)]
			for i := range s.XMM {
				s.XMM[i] = laneXMM(r, e)
			}
			emit("pint", b, s)
		}
		for _, o := range []byte{0x03, 0x04, 0x07, 0x0B, 0x1C, 0x1D, 0x1E, 0x2B, 0x38, 0x39, 0x3A, 0x3B, 0x3C,
			0x3D, 0x3E, 0x3F, 0x40, 0x28, 0x29, 0x37, 0x41} {
			d, sr := r.IntN(16), r.IntN(16)
			b := legacyRR(p66, []byte{0x0F, 0x38, o}, false, d, sr)
			s := baseState(r)
			e := []int{8, 16, 32, 64}[r.IntN(4)]
			for i := range s.XMM {
				s.XMM[i] = laneXMM(r, e)
			}
			emit("pint38", b, s)
		}
		// packed floating point under the MXCSR variants
		type fop struct {
			pre []byte
			op  []byte
			w   int
			imm bool
		}
		var fops []fop
		for _, o := range []byte{0x51, 0x58, 0x59, 0x5C, 0x5D, 0x5E, 0x5F, 0xC2, 0x5A, 0x5B} {
			fops = append(fops, fop{nil, []byte{0x0F, o}, 32, o == 0xC2}, fop{p66, []byte{0x0F, o}, 64, o == 0xC2})
		}
		fops = append(fops, fop{[]byte{0xF3}, []byte{0x0F, 0x5B}, 32, false}, fop{p66, []byte{0x0F, 0xE6}, 64, false},
			fop{[]byte{0xF2}, []byte{0x0F, 0xE6}, 64, false}, fop{[]byte{0xF3}, []byte{0x0F, 0xE6}, 64, false},
			fop{p66, []byte{0x0F, 0x7C}, 64, false}, fop{[]byte{0xF2}, []byte{0x0F, 0x7C}, 32, false},
			fop{p66, []byte{0x0F, 0x7D}, 64, false}, fop{[]byte{0xF2}, []byte{0x0F, 0x7D}, 32, false},
			fop{p66, []byte{0x0F, 0xD0}, 64, false}, fop{[]byte{0xF2}, []byte{0x0F, 0xD0}, 32, false},
			fop{p66, []byte{0x0F, 0x3A, 0x08}, 32, true}, fop{p66, []byte{0x0F, 0x3A, 0x09}, 64, true})
		for _, f := range fops {
			d, sr := r.IntN(16), r.IntN(16)
			var imm []byte
			if f.imm {
				if f.op[1] == 0x3A {
					imm = []byte{byte(round % 16)}
				} else {
					imm = []byte{byte(round % 8)}
				}
			}
			b := legacyRR(f.pre, f.op, false, d, sr, imm...)
			s := baseState(r)
			info := fpInfo{width: f.w, packed: true}
			for i := range s.XMM {
				s.XMM[i] = fpXMM(r, info)
			}
			if d != sr && r.IntN(2) == 0 {
				for l := 0; l < 128/f.w; l++ {
					fpLane(&s.XMM[sr], f.w, l, fpPair(r, f.w, fpLaneGet(s.XMM[d], f.w, l)))
				}
			}
			for k := 0; k < 22; k++ {
				t := s
				var m uint32
				if k < 16 {
					m = uint32(k&3)<<13 | 0x3F<<7
					if k&4 != 0 {
						m |= 1 << 15
					}
					if k&8 != 0 {
						m |= 1 << 6
					}
					if r.IntN(3) == 0 {
						m |= uint32(r.IntN(64))
					}
				} else {
					e := k - 16
					m = uint32(r.IntN(4))<<13 | (0x3F&^(1<<e))<<7
					if r.IntN(4) == 0 {
						m |= 1 << 15
					}
					if r.IntN(4) == 0 {
						m |= 1 << 6
					}
				}
				t.SetMXCSR(m)
				emit("sse-fp", b, t)
			}
		}
		// CRC32 at every width
		for _, f := range [][]byte{{0xF2}, {0xF2, 0x48}, {0x66, 0xF2}} {
			for _, o := range []byte{0xF0, 0xF1} {
				d, sr := randReg(r, true), randReg(r, true)
				pre := f
				if len(f) == 2 && f[1] == 0x48 {
					pre = []byte{0xF2}
				}
				var rex []byte
				w := 32
				if len(f) == 2 && f[1] == 0x48 {
					w = 64
				}
				rex = rexFor(w, d, 0, sr, false)
				b := cat(pre, rex, []byte{0x0F, 0x38, o, modrmRR(d, sr)})
				if f[0] == 0x66 {
					b = cat([]byte{0x66, 0xF2}, rex, []byte{0x0F, 0x38, o, modrmRR(d, sr)})
				}
				s := baseState(r)
				emit("crc32", b, s)
			}
		}
	}
	return out
}
