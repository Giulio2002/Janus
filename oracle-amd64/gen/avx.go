package gen

import (
	"math/rand/v2"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
	"golang.org/x/arch/x86/x86asm"
)

// AVX, AVX2 and packed FMA3 on VEX-128/256 with the YMM state (WP-F),
// Janus/Amd64/{InstrAVX,DecodeAVX,ExecAVX}.lean.

// AVXClasses are the WP-F classes (x86asm mnemonics, lower case).
var AVXClasses = strings.Fields(`vaddps vaddpd vaddss vaddsd vsubps vsubpd vsubss vsubsd vmulps vmulpd
	vmulss vmulsd vdivps vdivpd vdivss vdivsd vminps vminpd vminss vminsd vmaxps vmaxpd vmaxss vmaxsd
	vsqrtps vsqrtpd vsqrtss vsqrtsd
	vunpcklpd vunpckhpd vunpcklps vunpckhps vpunpcklbw vpunpcklwd vpunpckldq vpunpcklqdq vpunpckhbw
	vpunpckhwd vpunpckhdq vpunpckhqdq vpacksswb vpackssdw vpackuswb vpackusdw vpcmpgtb vpcmpgtw
	vpcmpgtd vpcmpgtq vpcmpeqw vpcmpeqd vpcmpeqq vpsrlw vpsrld vpsrlq vpsraw vpsrad vpsllw vpslld
	vpsllq vpsrldq vpslldq vpaddb vpaddw vpaddd vpaddq vpsubb vpsubw vpsubd vpsubq vpaddsb vpaddsw
	vpaddusb vpaddusw vpsubsb vpsubsw vpsubusb vpsubusw vpmullw vpmulld vpmulhw vpmulhuw vpmuludq
	vpmuldq vpmaddwd vpmaddubsw vpmulhrsw vpminub vpminuw vpminud vpminsb vpminsw vpminsd vpmaxub
	vpmaxuw vpmaxud vpmaxsb vpmaxsw vpmaxsd vpandn vpavgb vpavgw vpsadbw vphaddw vphaddd vphaddsw
	vphsubw vphsubd vphsubsw vpsignw vpsignd vpabsb vpabsw vpabsd vpshufb vpsignb
	vmovups vmovupd vmovaps vmovapd vmovntps vmovntpd vmovntdqa vlddqu vmovss vmovsd vmovlps vmovlpd
	vmovhps vmovhpd vmovhlps vmovlhps vmovsldup vmovshdup vmovddup vmovd vmovq
	vcvtsi2ss vcvtsi2sd vcvttss2si vcvtss2si vcvttsd2si vcvtsd2si vucomiss vucomisd vcomiss vcomisd
	vmovmskps vmovmskpd vandps vandpd vorps vorpd vxorps vxorpd vandnps vandnpd vcvtps2pd vcvtpd2ps
	vcvtss2sd vcvtsd2ss vcvtdq2ps vcvtps2dq vcvttps2dq vcvttpd2dq vcvtdq2pd vcvtpd2dq
	vpshufd vpshufhw vpshuflw vhaddpd vhsubpd vhaddps vhsubps vaddsubpd vaddsubps vcmpps vcmppd
	vcmpss vcmpsd vshufps vshufpd vpinsrb vpinsrw vpinsrd vpinsrq vpextrb vpextrw vpextrd vpextrq
	vextractps vinsertps vzeroall
	vpmovsxbw vpmovsxbd vpmovsxbq vpmovsxwd vpmovsxwq vpmovsxdq vpmovzxbw vpmovzxbd vpmovzxbq
	vpmovzxwd vpmovzxwq vpmovzxdq vphminposuw vpermilps vpermilpd vtestps vtestpd vpermps vpermd
	vpermq vpermpd vperm2f128 vperm2i128 vbroadcastss vbroadcastsd vpbroadcastw vpbroadcastd
	vpbroadcastq vbroadcastf128 vbroadcasti128 vmaskmovps vmaskmovpd vpmaskmovd vpmaskmovq vpsrlvd
	vpsrlvq vpsravd vpsllvd vpsllvq vpgatherdd vpgatherdq vpgatherqd vpgatherqq vgatherdps vgatherdpd
	vgatherqps vgatherqpd vpblendd vroundps vroundpd vroundss vroundsd vblendps vblendpd vpblendw
	vpalignr vmpsadbw vinsertf128 vinserti128 vextractf128 vextracti128 vblendvps vblendvpd vpblendvb
	vpcmpestrm vpcmpestri vpcmpistrm vpcmpistri vpcmpestrm64 vpcmpestri64 vcvtph2ps vcvtps2ph`)

// AVXFMAClasses are the 72 packed FMA3 classes.
var AVXFMAClasses []string

// avxFP are the floating-point WP-F classes: lane width, packed, integer source.
var avxFP = map[string]fpInfo{}

var avxSet = map[string]bool{}

func init() {
	for _, n := range []string{"vfmadd", "vfmsub", "vfnmadd", "vfnmsub", "vfmaddsub", "vfmsubadd"} {
		for _, f := range []string{"132", "213", "231"} {
			for _, t := range []string{"ps", "pd"} {
				AVXFMAClasses = append(AVXFMAClasses, n+f+t)
			}
		}
	}
	for _, m := range AVXClasses {
		Modeled[m] = true
		avxSet[m] = true
	}
	for _, m := range AVXFMAClasses {
		Modeled[m] = true
		avxSet[m] = true
		w := 32
		if strings.HasSuffix(m, "pd") {
			w = 64
		}
		avxFP[m] = fpInfo{width: w, packed: true, fma: true}
	}
	// the scalar FMA3 classes are WP-B's; the VEX scalar and packed FP classes:
	for _, m := range strings.Fields(`vaddss vsubss vmulss vdivss vminss vmaxss vsqrtss vcmpss vroundss
		vucomiss vcomiss vcvttss2si vcvtss2si vcvtss2sd`) {
		avxFP[m] = fpInfo{width: 32}
	}
	for _, m := range strings.Fields(`vaddsd vsubsd vmulsd vdivsd vminsd vmaxsd vsqrtsd vcmpsd vroundsd
		vucomisd vcomisd vcvttsd2si vcvtsd2si vcvtsd2ss`) {
		avxFP[m] = fpInfo{width: 64}
	}
	for _, m := range strings.Fields(`vaddps vsubps vmulps vdivps vminps vmaxps vsqrtps vcmpps vroundps
		vhaddps vhsubps vaddsubps vcvtps2pd vcvtps2dq vcvttps2dq`) {
		avxFP[m] = fpInfo{width: 32, packed: true}
	}
	for _, m := range strings.Fields(`vaddpd vsubpd vmulpd vdivpd vminpd vmaxpd vsqrtpd vcmppd vroundpd
		vhaddpd vhsubpd vaddsubpd vcvtpd2ps vcvtpd2dq vcvttpd2dq`) {
		avxFP[m] = fpInfo{width: 64, packed: true}
	}
	avxFP["vcvtsi2ss"] = fpInfo{width: 32, gprSrc: true}
	avxFP["vcvtsi2sd"] = fpInfo{width: 64, gprSrc: true}
	avxFP["vcvtdq2ps"] = fpInfo{width: 32, packed: true}
	avxFP["vcvtdq2pd"] = fpInfo{width: 64, packed: true}
	avxFP["vcvtps2ph"] = fpInfo{width: 32, packed: true}
	avxFP["vcvtph2ps"] = fpInfo{width: 16, packed: true}
	for m, i := range avxFP {
		// IsFP: several MXCSR settings per state (the FP setup itself is setupAVX's)
		if _, ok := fpClasses[m]; !ok {
			w := i.width
			if w == 16 {
				w = 32 // setupFP's lanes; setupAVX plants the binary16 values
			}
			fpClasses[m] = fpInfo{width: w, packed: i.packed, gprSrc: i.gprSrc}
		}
	}
}

// AVXRegexp matches every WP-F class (for `harvest -only`).
func AVXRegexp() string {
	return "^(" + strings.Join(AVXClasses, "|") + "|" + strings.Join(AVXFMAClasses, "|") + ")$"
}

// AvxSpec is a targeted VEX family of WP-F: the encoding fields, and whether VEX.vvvv is an
// operand (three-operand forms: drawn uniformly; otherwise mostly 1111).
type AvxSpec struct {
	VexSpec
	ThreeOp bool
}

func avxSpecs() []AvxSpec {
	var s []AvxSpec
	add := func(name string, mp, pp, op byte, three bool, mods ...int) {
		if len(mods) == 0 {
			mods = []int{1, 2, 0}
		}
		for _, m := range mods {
			s = append(s, AvxSpec{VexSpec{name, mp, pp, op, m}, three})
		}
	}
	// map 0F
	for _, op := range []byte{0x58, 0x59, 0x5C, 0x5D, 0x5E, 0x5F} {
		for pp := byte(0); pp < 4; pp++ {
			add("avx/fp", 1, pp, op, true)
		}
	}
	for pp := byte(0); pp < 4; pp++ {
		add("avx/fp", 1, pp, 0x51, pp >= 2)
		add("avx/fp", 1, pp, 0x5A, pp >= 2)
		add("avx/fp", 1, pp, 0xC2, true)
		add("avx/fp", 1, pp, 0x5B, false)
		add("avx/fp", 1, pp, 0xE6, false)
		add("avx/mov", 1, pp, 0x10, pp >= 2)
		add("avx/mov", 1, pp, 0x11, pp >= 2)
		add("avx/mov", 1, pp, 0x12, true)
		add("avx/mov", 1, pp, 0x13, false)
		add("avx/mov", 1, pp, 0x16, true)
		add("avx/mov", 1, pp, 0x17, false)
		add("avx/cvt", 1, pp, 0x2A, true)
		add("avx/cvt", 1, pp, 0x2C, false)
		add("avx/cvt", 1, pp, 0x2D, false)
		add("avx/fp", 1, pp, 0x2E, false)
		add("avx/fp", 1, pp, 0x2F, false)
		add("avx/mov", 1, pp, 0x28, false)
		add("avx/mov", 1, pp, 0x29, false)
		add("avx/mov", 1, pp, 0x2B, false)
		add("avx/fp", 1, pp, 0x50, false)
		add("avx/fp", 1, pp, 0x7C, true)
		add("avx/fp", 1, pp, 0x7D, true)
		add("avx/fp", 1, pp, 0xD0, true)
		add("avx/int", 1, pp, 0x70, false)
		add("avx/mov", 1, pp, 0x7E, false)
	}
	for _, op := range []byte{0x14, 0x15, 0x54, 0x55, 0x56, 0x57, 0xC6} {
		add("avx/fp", 1, 0, op, true)
		add("avx/fp", 1, 1, op, true)
	}
	for op := 0x60; op <= 0x6D; op++ {
		add("avx/int", 1, 1, byte(op), true)
	}
	for _, op := range []byte{0x75, 0x76, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD8, 0xD9, 0xDA, 0xDC, 0xDD, 0xDE,
		0xDF, 0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE8, 0xE9, 0xEA, 0xEC, 0xED, 0xEE, 0xF1, 0xF2, 0xF3, 0xF4,
		0xF5, 0xF6, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE} {
		add("avx/int", 1, 1, op, true)
	}
	add("avx/mov", 1, 1, 0x6E, false)
	add("avx/mov", 1, 1, 0xD6, false)
	add("avx/mov", 1, 3, 0xF0, false)
	for _, op := range []byte{0x71, 0x72, 0x73} {
		add("avx/shift", 1, 1, op, true, 1, 1, 0)
	}
	add("avx/int", 1, 1, 0xC4, true)
	add("avx/int", 1, 1, 0xC5, false, 1, 0)
	add("avx/zero", 1, 0, 0x77, false, 0, 0)
	// neighbours that must be rejected
	for _, op := range []byte{0x52, 0x53, 0xF7, 0xAE} {
		add("avx/other", 1, 0, op, false, 0)
		add("avx/other", 1, 1, op, false, 0)
	}
	add("avx/other", 1, 0, 0x60, true, 0)
	// map 0F38 (66)
	for op := 0x00; op <= 0x0F; op++ {
		add("avx/int38", 2, 1, byte(op), op < 0x0E)
	}
	for _, op := range []byte{0x16, 0x18, 0x19, 0x1A, 0x1C, 0x1D, 0x1E, 0x2A, 0x36, 0x41, 0x58, 0x59, 0x5A, 0x79,
		0x13} {
		add("avx/int38", 2, 1, op, op == 0x16 || op == 0x36)
	}
	for op := 0x20; op <= 0x25; op++ {
		add("avx/pmovx", 2, 1, byte(op), false)
		add("avx/pmovx", 2, 1, byte(op+0x10), false)
	}
	for _, op := range []byte{0x28, 0x29, 0x2B, 0x37, 0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F, 0x40,
		0x45, 0x46, 0x47} {
		add("avx/int38", 2, 1, op, true)
	}
	for _, op := range []byte{0x2C, 0x2D, 0x2E, 0x2F, 0x8C, 0x8E} {
		add("avx/maskmov", 2, 1, op, true, 2, 2, 2, 0)
	}
	for _, op := range []byte{0x90, 0x91, 0x92, 0x93} {
		add("avx/gather", 2, 1, op, true, 2, 2, 2, 2, 0)
	}
	for hi := 0x90; hi <= 0xB0; hi += 0x10 {
		for _, lo := range []int{6, 7, 8, 0xA, 0xC, 0xE} {
			add("avx/fma", 2, 1, byte(hi|lo), true)
		}
	}
	// map 0F3A (66)
	for _, op := range []byte{0x00, 0x01, 0x02, 0x04, 0x05, 0x06, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
		0x0F, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x20, 0x21, 0x22, 0x38, 0x39, 0x42, 0x46, 0x4A, 0x4B, 0x4C,
		0x60, 0x61, 0x62, 0x63, 0x40, 0x41, 0x44, 0x1D} {
		three := op == 0x02 || op == 0x06 || op == 0x0A || op == 0x0B || (op >= 0x0C && op <= 0x0F) ||
			op == 0x18 || op == 0x20 || op == 0x21 || op == 0x22 || op == 0x38 || op == 0x42 || op == 0x46 ||
			op == 0x4A || op == 0x4B || op == 0x4C
		add("avx/imm", 3, 1, op, three)
	}
	return s
}

// AVXSpecs are the targeted WP-F VEX families.
var AVXSpecs = avxSpecs()

// AVXTargeted produces one encoding of sp: VEX.L uniform, VEX.W uniform, VEX.vvvv uniform for
// three-operand forms (mostly 1111 otherwise), sometimes a stray prefix, another map or pp, the
// 2-byte form when it can express the fields; then ModRM (by sp.Mod3), SIB, displacement and
// immediate bytes.
func AVXTargeted(r *rand.Rand, sp AvxSpec) []byte {
	var out []byte
	if r.IntN(24) == 0 {
		out = append(out, []byte{0x66, 0xF2, 0xF3, 0xF0, 0x40, 0x48, 0x2E, 0x64, 0x67}[r.IntN(9)])
	}
	rr, xx, bb := byte(r.IntN(2)), byte(r.IntN(2)), byte(r.IntN(2))
	w := byte(r.IntN(2))
	vvvv := byte(0)
	if sp.ThreeOp || r.IntN(8) == 0 {
		vvvv = byte(r.IntN(16))
	}
	l := byte(r.IntN(2))
	mp, pp := sp.Map, sp.PP
	if r.IntN(32) == 0 {
		mp = byte(r.IntN(4))
	}
	if r.IntN(32) == 0 {
		pp = byte(r.IntN(4))
	}
	if mp == 1 && xx == 0 && bb == 0 && w == 0 && r.IntN(2) == 0 {
		out = append(out, 0xC5, (1-rr)<<7|(^vvvv&15)<<3|l<<2|pp)
	} else {
		out = append(out, 0xC4, (1-rr)<<7|(1-xx)<<6|(1-bb)<<5|mp, w<<7|(^vvvv&15)<<3|l<<2|pp)
	}
	out = append(out, sp.Op)
	modrm := byte(r.IntN(256))
	switch sp.Mod3 {
	case 1:
		modrm |= 0xC0
	case 2:
		if modrm>>6 == 3 {
			modrm &^= 0xC0
		}
		if sp.Name == "avx/gather" && r.IntN(8) != 0 {
			modrm = modrm&^7 | 4 // VSIB
		}
	default:
		if r.IntN(3) == 0 {
			modrm |= 0xC0
		}
	}
	tail := make([]byte, 12)
	for i := range tail {
		tail[i] = byte(r.IntN(256))
		if r.IntN(2) == 0 && i > 0 {
			tail[i] = []byte{0, 0, 0xff, 1, 0x20, 0x10, 0x80, 0xe0, 7, 0x1b, 0x4e, 0x55, 0x31, 0x0f}[r.IntN(14)]
		}
	}
	tail[0] = modrm
	out = append(out, tail...)
	return trim(out)
}

// vecArg is the vector register number of an x86asm argument (XMM or YMM), or -1.
func vecArg(a x86asm.Arg) int {
	if g, ok := a.(x86asm.Reg); ok {
		switch {
		case g >= x86asm.X0 && g <= x86asm.X15:
			return int(g - x86asm.X0)
		case g >= x86asm.Y0 && g <= x86asm.Y15:
			return int(g - x86asm.Y0)
		}
	}
	return -1
}

// avxElem is the element width the class's lanes are steered at.
func avxElem(cls string) int {
	c := strings.TrimPrefix(cls, "v")
	switch {
	case strings.HasPrefix(c, "pmovsx") || strings.HasPrefix(c, "pmovzx"):
		return []int{8, 16, 32}[strings.Index("bwd", c[6:7])]
	case strings.HasPrefix(c, "pbroadcast"):
		return map[string]int{"w": 16, "d": 32, "q": 64}[c[10:]]
	case strings.HasSuffix(c, "vd") || strings.HasSuffix(c, "dd") || c == "permd" || c == "pblendd":
		return 32
	case strings.HasSuffix(c, "vq") || c == "permq":
		return 64
	}
	return sseElem(c)
}

// vec256 is a 256-bit value (four 64-bit words) of e-bit lane values.
func vec256(r *rand.Rand, e int) [4]uint64 {
	lo, hi := laneXMM(r, e), laneXMM(r, e)
	return [4]uint64{lo[0], lo[1], hi[0], hi[1]}
}

func setVec(s *State, n int, v [4]uint64) {
	s.XMM[n] = [2]uint64{v[0], v[1]}
	s.YMMH[n] = [2]uint64{v[2], v[3]}
}

func getVec(s *State, n int) [4]uint64 {
	return [4]uint64{s.XMM[n][0], s.XMM[n][1], s.YMMH[n][0], s.YMMH[n][1]}
}

// lane sets element i (width e) of v to x.
func lane(v *[4]uint64, e, i int, x uint64) {
	if e == 64 {
		v[i] = x
		return
	}
	bit := i * e
	m := uint64(1)<<uint(e) - 1
	v[bit/64] = v[bit/64]&^(m<<uint(bit%64)) | (x&m)<<uint(bit%64)
}

func laneGet(v [4]uint64, e, i int) uint64 {
	if e == 64 {
		return v[i]
	}
	bit := i * e
	return v[bit/64] >> uint(bit%64) & (uint64(1)<<uint(e) - 1)
}

// fpVec is a 256-bit value with IEEE edge values in every w-bit lane.
func fpVec(r *rand.Rand, w int) [4]uint64 {
	var v [4]uint64
	for i := 0; i < 256/w; i++ {
		lane(&v, w, i, FPEdge(r, w))
	}
	return v
}

// maskVec is a mask with the top bit of each e-bit element random (mostly all set or all
// clear, the elements' low bits random).
func maskVec(r *rand.Rand, e int) [4]uint64 {
	v := [4]uint64{r.Uint64(), r.Uint64(), r.Uint64(), r.Uint64()}
	mode := r.IntN(4)
	for i := 0; i < 256/e; i++ {
		x := laneGet(v, e, i) &^ (1 << uint(e-1))
		set := r.IntN(2) == 0
		if mode == 0 {
			set = true
		} else if mode == 1 {
			set = false
		}
		if set {
			x |= 1 << uint(e-1)
		}
		lane(&v, e, i, x)
	}
	return v
}

func plant256(s *State, ea uint64, v [4]uint64, n int) {
	plantLE(s, ea, [2]uint64{v[0], v[1]}, min(n, 16))
	if n > 16 {
		plantLE(s, ea+16, [2]uint64{v[2], v[3]}, n-16)
	}
}

// setupAVX steers the operands of the WP-F classes: element edge values in both halves of the
// YMM registers and in the memory operand, IEEE edge values (paired across the sources) for the
// floating-point classes, crafted FMA addends, count vectors for the variable shifts, index and
// mask vectors for the permutes, masked moves (also at the end of the buffer, so that
// masked-off elements fall outside it) and gathers, string operands and lengths, aligned
// operands for the aligned moves.
func setupAVX(r *rand.Rand, s *State, inst x86asm.Inst, cls string) {
	if !avxSet[cls] {
		return
	}
	info, isFP := avxFP[cls]
	e := avxElem(cls)
	if isFP {
		e = info.width
	}
	for i := 0; i < 16; i++ {
		if isFP {
			v := fpVec(r, info.width)
			if strings.HasPrefix(cls, "vcvtdq2") || info.gprSrc {
				for k := 0; k < 8; k++ {
					lane(&v, 32, k, FPInt(r))
				}
			}
			setVec(s, i, v)
		} else if r.IntN(4) != 0 {
			setVec(s, i, vec256(r, e))
		}
	}
	var vregs []int
	var mem *x86asm.Mem
	for _, a := range inst.Args {
		if a == nil {
			break
		}
		if n := vecArg(a); n >= 0 {
			vregs = append(vregs, n)
		}
		if m, ok := a.(x86asm.Mem); ok {
			mm := m
			mem = &mm
		}
	}
	// FP: pair the two sources lane by lane (same exponent, ulp neighbours, ...)
	if isFP && len(vregs) >= 2 && r.IntN(10) < 5 {
		a, b := vregs[len(vregs)-2], vregs[len(vregs)-1]
		if len(vregs) == 3 {
			a, b = vregs[1], vregs[2]
		}
		va, vb := getVec(s, a), getVec(s, b)
		for k := 0; k < 256/info.width; k++ {
			lane(&vb, info.width, k, fpPair(r, info.width, laneGet(va, info.width, k)))
		}
		if a != b {
			setVec(s, b, vb)
		}
	}
	// FMA: crafted addends per lane
	if info.fma && len(vregs) == 3 {
		ra, rb, rc := fmaRoles(cls)
		va, vb, vc := getVec(s, vregs[ra]), getVec(s, vregs[rb]), getVec(s, vregs[rc])
		for k := 0; k < 256/info.width; k++ {
			if r.IntN(10) < 6 {
				lane(&vc, info.width, k, fmaAddend(r, info.width, laneGet(va, info.width, k), laneGet(vb, info.width, k)))
			}
		}
		if vregs[rc] != vregs[ra] && vregs[rc] != vregs[rb] {
			setVec(s, vregs[rc], vc)
		}
	}
	switch {
	case strings.HasPrefix(cls, "vpsllv") || strings.HasPrefix(cls, "vpsrlv") || cls == "vpsravd":
		if len(vregs) == 3 && r.IntN(4) != 0 {
			var c [4]uint64
			for k := 0; k < 256/e; k++ {
				lane(&c, e, k, []uint64{0, 1, 2, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 1 << 31, ^uint64(0), uint64(r.IntN(70))}[r.IntN(16)])
			}
			setVec(s, vregs[2], c)
		}
	case cls == "vpermd" || cls == "vpermps":
		if len(vregs) >= 2 && r.IntN(2) == 0 {
			var c [4]uint64
			for k := 0; k < 8; k++ {
				lane(&c, 32, k, uint64(r.IntN(8))|uint64(r.IntN(4))<<uint(3+r.IntN(29)))
			}
			setVec(s, vregs[1], c)
		}
	case cls == "vpermilps" || cls == "vpermilpd":
		if len(vregs) == 3 && r.IntN(2) == 0 {
			var c [4]uint64
			for k := 0; k < 256/e; k++ {
				lane(&c, e, k, r.Uint64())
			}
			setVec(s, vregs[2], c)
		}
	case cls == "vpblendvb" || cls == "vblendvps" || cls == "vblendvpd":
		if len(vregs) == 4 && r.IntN(4) != 0 {
			setVec(s, vregs[3], maskVec(r, e))
		}
	case strings.HasPrefix(cls, "vpcmpestr") || strings.HasPrefix(cls, "vpcmpistr"):
		words := false
		if im, ok := inst.Args[2].(x86asm.Imm); ok {
			words = im&1 == 1
		}
		for i := 0; i < 16; i++ {
			s.XMM[i] = strXMM(r, words)
		}
		if len(vregs) == 2 && r.IntN(4) == 0 {
			s.XMM[vregs[0]] = shr128(s.XMM[vregs[1]], uint(8*r.IntN(8)))
		}
		s.Regs[0], s.Regs[2] = strLen(r), strLen(r)
	case cls == "vpsllw" || cls == "vpslld" || cls == "vpsllq" || cls == "vpsrlw" || cls == "vpsrld" ||
		cls == "vpsrlq" || cls == "vpsraw" || cls == "vpsrad":
		if len(inst.Args) > 2 && inst.Args[2] != nil {
			if _, isImm := inst.Args[2].(x86asm.Imm); !isImm {
				c := []uint64{0, 1, 2, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 255, 1 << 32, 1 << 63}[r.IntN(17)]
				hi := []uint64{0, 0, r.Uint64(), 1}[r.IntN(4)]
				if x := vecArg(inst.Args[2]); x >= 0 {
					s.XMM[x] = [2]uint64{c, hi}
				} else if mem != nil {
					if ea, ok := effAddr(s, inst, *mem); ok {
						plantLE(s, ea, [2]uint64{c, hi}, 16)
					}
				}
			}
		}
	}
	if strings.Contains(cls, "gather") {
		setupGather(r, s, inst, cls)
		return
	}
	if strings.Contains(cls, "maskmov") {
		setupMaskmov(r, s, inst, cls, vregs, mem)
		return
	}
	if mem == nil {
		return
	}
	n := inst.MemBytes
	if n <= 0 || n > 32 {
		n = 32
	}
	// aligned moves: mostly align the operand
	if cls == "vmovaps" || cls == "vmovapd" || cls == "vmovntps" || cls == "vmovntpd" || cls == "vmovntdqa" {
		if ea, ok := effAddr(s, inst, *mem); ok && ea >= L.DataBase && ea < L.DataBase+L.DataSize && r.IntN(4) != 0 {
			if bn, _, bok := regNum(mem.Base); bok && bn != 4 {
				s.Regs[bn] -= ea & uint64(n-1)
			}
		}
	}
	if ea, ok := effAddr(s, inst, *mem); ok && r.IntN(3) != 0 {
		var v [4]uint64
		switch {
		case isFP && info.gprSrc:
			v = [4]uint64{FPInt(r), FPInt(r)}
		case isFP && strings.HasPrefix(cls, "vcvtdq2"):
			for k := 0; k < 8; k++ {
				lane(&v, 32, k, FPInt(r))
			}
		case isFP:
			v = fpVec(r, info.width)
			if len(vregs) >= 2 && r.IntN(2) == 0 {
				va := getVec(s, vregs[len(vregs)-1])
				for k := 0; k < 256/info.width; k++ {
					lane(&v, info.width, k, fpPair(r, info.width, laneGet(va, info.width, k)))
				}
			}
		default:
			v = vec256(r, e)
		}
		plant256(s, ea, v, n)
	}
}

// setupGather steers a VSIB gather: the base register near the middle of the buffer (or the
// displacement-only form), small signed index elements (sometimes one far outside the buffer),
// a mask with mixed top bits.
func setupGather(r *rand.Rand, s *State, inst x86asm.Inst, cls string) {
	var dst, mask int = -1, -1
	var m *x86asm.Mem
	for i, a := range inst.Args {
		if a == nil {
			break
		}
		if mm, ok := a.(x86asm.Mem); ok {
			x := mm
			m = &x
		} else if n := vecArg(a); n >= 0 {
			if i == 0 {
				dst = n
			} else {
				mask = n
			}
		}
	}
	if m == nil {
		return
	}
	idx := vecArg(m.Index)
	e := 32
	if strings.HasSuffix(cls, "dq") || strings.HasSuffix(cls, "qq") || strings.HasSuffix(cls, "pd") {
		e = 64
	}
	ie := 32
	if strings.Contains(cls, "gatherq") {
		ie = 64
	}
	scale := uint64(m.Scale)
	if scale == 0 {
		scale = 1
	}
	target := L.DataBase + 1024 + uint64(r.IntN(2048))
	if bn, _, ok := regNum(m.Base); ok && bn != 4 {
		s.Regs[bn] = target - uint64(m.Disp)
	}
	if idx >= 0 {
		var v [4]uint64
		for k := 0; k < 256/ie; k++ {
			x := uint64(int64(r.IntN(129) - 64))
			if r.IntN(24) == 0 {
				x = r.Uint64()
			}
			lane(&v, ie, k, x)
		}
		if r.IntN(4) != 0 && idx != dst && idx != mask {
			setVec(s, idx, v)
		}
	}
	if mask >= 0 && mask != idx {
		setVec(s, mask, maskVec(r, e))
	}
	_ = dst
}

// setupMaskmov steers a masked move: the mask vector with mixed top bits; the operand inside
// the buffer, or straddling its end (or start) so that only some elements are accessible.
func setupMaskmov(r *rand.Rand, s *State, inst x86asm.Inst, cls string, vregs []int, mem *x86asm.Mem) {
	e := 32
	if strings.HasSuffix(cls, "pd") || strings.HasSuffix(cls, "q") {
		e = 64
	}
	if len(vregs) >= 2 {
		// the mask is VEX.vvvv, the middle operand: vregs = [dst, mask] (load) or [mask, src]
		mk := vregs[1]
		if _, ok := inst.Args[0].(x86asm.Mem); ok {
			mk = vregs[0]
		}
		setVec(s, mk, maskVec(r, e))
	}
	if mem == nil {
		return
	}
	bn, _, ok := regNum(mem.Base)
	if !ok || bn == 4 {
		return
	}
	in, _, iok := regNum(mem.Index)
	if iok {
		s.Regs[in] = 0
	}
	var target uint64
	switch r.IntN(4) {
	case 0:
		target = L.DataBase + L.DataSize - uint64(4*(1+r.IntN(8)))
	case 1:
		target = L.DataBase - uint64(4*(1+r.IntN(8)))
	default:
		target = L.DataBase + uint64(r.IntN(L.DataSize-32))
	}
	s.Regs[bn] = target - uint64(mem.Disp)
}

// AVXEdges are the systematic WP-F families, per round: the packed floating-point operations
// and packed FMA at both lengths on IEEE edge values under MXCSR settings drawn from the 16
// RC x FTZ/DAZ combinations (all masked) and each exception unmasked alone; VCMPPS/PD/SS/SD
// under every one of the 32 predicates; every VPERM2I128/VPERM2F128, VPERMQ, VPBLENDD, VSHUFPD
// and VPERMILPD immediate class; VEX.128 forms after which the upper halves of every register
// are nonzero (the zero-upper rule).
func AVXEdges(r *rand.Rand, n int) []EdgeCase {
	var out []EdgeCase
	emit := func(class string, b []byte) []State {
		if !OK(b) {
			return nil
		}
		s := Setup(r, b)
		out = append(out, EdgeCase{"edge/" + class, b, s})
		return []State{s}
	}
	mx := func(k int) uint32 {
		if k < 16 {
			m := uint32(k&3)<<13 | 0x3F<<7
			if k&4 != 0 {
				m |= 1 << 15
			}
			if k&8 != 0 {
				m |= 1 << 6
			}
			if r.IntN(3) == 0 {
				m |= uint32(r.IntN(64))
			}
			return m
		}
		e := k - 16
		m := uint32(r.IntN(4))<<13 | (0x3F&^(1<<e))<<7
		if r.IntN(4) == 0 {
			m |= 1 << 15
		}
		if r.IntN(4) == 0 {
			m |= 1 << 6
		}
		return m
	}
	rr := func() (int, int, int) {
		d, a, b := r.IntN(16), r.IntN(16), r.IntN(16)
		if r.IntN(4) != 0 {
			for a == d {
				a = r.IntN(16)
			}
			for b == d || b == a {
				b = r.IntN(16)
			}
		}
		return d, a, b
	}
	for round := 0; round < n; round++ {
		// packed FP arithmetic (0F 51 58 59 5C 5D 5E 5F, 7C 7D D0) and FMA (0F38 9x/Ax/Bx)
		type fop struct {
			mp, pp, op byte
			three      bool
		}
		var fops []fop
		for _, op := range []byte{0x58, 0x59, 0x5C, 0x5D, 0x5E, 0x5F, 0x51} {
			fops = append(fops, fop{1, 0, op, op != 0x51}, fop{1, 1, op, op != 0x51})
		}
		fops = append(fops, fop{1, 1, 0x7C, true}, fop{1, 3, 0x7C, true}, fop{1, 1, 0xD0, true}, fop{1, 3, 0xD0, true},
			fop{1, 0, 0x5A, false}, fop{1, 1, 0x5A, false}, fop{1, 1, 0x5B, false}, fop{1, 2, 0x5B, false},
			fop{1, 1, 0xE6, false}, fop{1, 3, 0xE6, false}, fop{1, 2, 0xE6, false}, fop{1, 0, 0x5B, false})
		for hi := byte(0x90); hi <= 0xB0; hi += 0x10 {
			for _, lo := range []byte{6, 7, 8, 0xA, 0xC, 0xE} {
				fops = append(fops, fop{2, 1, hi | lo, true})
			}
		}
		for _, f := range fops {
			d, a, b := rr()
			w := r.IntN(2)
			if f.mp == 1 {
				w = 0
			}
			v := a
			if !f.three {
				v = 0
			}
			rex := d>>3<<2 | b>>3 | w<<3
			bs := vexEnc(rex, f.mp, v, r.IntN(2), f.pp, f.op, modrmRR(d, b))
			for _, s := range emit("avx-fp", bs) {
				for k := 0; k < 3; k++ {
					t := s
					t.Init = append([][2]int(nil), s.Init...)
					t.SetMXCSR(mx(r.IntN(22)))
					out = append(out, EdgeCase{"edge/avx-fp", bs, t})
				}
			}
		}
		// VCMPPS/PD/SS/SD: all 32 predicates
		for p := 0; p < 32; p++ {
			pp := byte(r.IntN(4))
			d, a, b := rr()
			l := r.IntN(2)
			if pp >= 2 {
				l = 0
			}
			bs := vexEnc(d>>3<<2|b>>3, 1, a, l, pp, 0xC2, modrmRR(d, b), byte(p))
			emit("avx-cmp", bs)
		}
		// permute / blend immediates
		for _, f := range []struct{ op byte }{{0x06}, {0x46}, {0x00}, {0x01}, {0x02}, {0x05}, {0x0C}, {0x0D}, {0x42}} {
			d, a, b := rr()
			w, l, v := 0, 1, a
			switch f.op {
			case 0x00, 0x01:
				w, v = 1, 0
			case 0x05:
				v, l = 0, r.IntN(2)
			case 0x02, 0x0C, 0x0D, 0x42:
				l = r.IntN(2)
			}
			bs := vexEnc(d>>3<<2|b>>3|w<<3, 3, v, l, 1, f.op, modrmRR(d, b), byte(r.IntN(256)))
			emit("avx-imm", bs)
		}
		// VEX.128 integer forms with live upper halves (zero-upper)
		for _, op := range []byte{0xFE, 0xD4, 0xF8, 0x60, 0x6C, 0xDF, 0x76} {
			d, a, b := rr()
			bs := vexEnc(d>>3<<2|b>>3, 1, a, 0, 1, op, modrmRR(d, b))
			emit("avx-upper", bs)
		}
	}
	return out
}
