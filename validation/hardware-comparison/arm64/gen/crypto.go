package gen

import "math/rand/v2"

// The cryptographic-extension, CRC32, permute and scalar-DUP classes (Janus
// `CryptoInstr`, Janus/Arm64/DecodeCrypto.lean). Each class is the whole encoding group of the
// A64 tables, so the unallocated and UNDEFINED neighbours inside it (SM3/SM4, reserved sizes
// and opcodes) are classified and tested with it.
var CryptoClasses = []string{
	"crypto.sha3reg", "crypto.sha2reg", "crypto.sha512", "crypto.sha3",
	"simd.pmull", "simd.permute", "simd.dupscalar", "dpr.crc32",
}

// cryptoSpace is the fixed part of each class (classifyCrypto): a quarter of the generated
// words are fully random below it, the rest come from the targeted generators.
var cryptoSpace = map[string][][2]uint32{
	"crypto.sha3reg": {{0xFF208C00, 0x5E000000}},
	"crypto.sha2reg": {{0xFF3E0C00, 0x5E280800}},
	"crypto.sha512":  {{0xFFE0B000, 0xCE608000}, {0xFFFFF000, 0xCEC08000}},
	"crypto.sha3":    {{0xFF808000, 0xCE000000}, {0xFFE00000, 0xCE800000}},
	"simd.pmull":     {{0xBF20FC00, 0x0E20E000}},
	"simd.permute":   {{0xBF208C00, 0x0E000800}},
	"simd.dupscalar": {{0xDFE08400, 0x5E000400}},
	"dpr.crc32":      {{0x7FE0E000, 0x1AC04000}},
}

func init() {
	Classes = append(Classes, CryptoClasses...)
	for k, g := range cryptoTargeted {
		g, sp := g, cryptoSpace[k]
		Targeted[k] = func(r *rand.Rand) uint32 {
			if r.IntN(4) == 0 {
				m := sp[r.IntN(len(sp))]
				return r.Uint32()&^m[0] | m[1]
			}
			return g(r)
		}
	}
}

// classifyCrypto returns the crypto class of w, or "" (Classify calls it first).
func classifyCrypto(w uint32) string {
	switch {
	case w&0xFF208C00 == 0x5E000000: // crypto three-register SHA (any size)
		return "crypto.sha3reg"
	case w&0xFF3E0C00 == 0x5E280800: // crypto two-register SHA (any size)
		return "crypto.sha2reg"
	case w&0xFFE0B000 == 0xCE608000, w&0xFFFFF000 == 0xCEC08000: // SHA512 three/two-register (+ SM3PARTW, SM4E, SM4EKEY)
		return "crypto.sha512"
	case w&0xFF808000 == 0xCE000000, w&0xFFE00000 == 0xCE800000: // four-register (EOR3, BCAX, SM3SS1), XAR
		return "crypto.sha3"
	case w&0xBF20FC00 == 0x0E20E000: // three different, U = 0, opcode 1110: PMULL
		return "simd.pmull"
	case w&0xBF208C00 == 0x0E000800: // permute
		return "simd.permute"
	case w&0xDFE08400 == 0x5E000400: // scalar copy (DUP element; op = 1 / imm4 != 0 unallocated)
		return "simd.dupscalar"
	case w&0x7FE0E000 == 0x1AC04000: // data processing (2 source), opcode 010xxx: CRC32
		return "dpr.crc32"
	}
	return ""
}

var cryptoTargeted = map[string]func(r *rand.Rand) uint32{
	"crypto.sha3reg": func(r *rand.Rand) uint32 {
		opc := uint32(r.IntN(7))
		size := uint32(0)
		if r.IntN(8) == 0 { // neighbours: opcode 111, other sizes
			opc, size = u(r, 3), u(r, 2)
		}
		return 0x5E000000 | size<<22 | vreg(r)<<16 | opc<<12 | vreg(r)<<5 | vreg(r)
	},
	"crypto.sha2reg": func(r *rand.Rand) uint32 {
		opc := uint32(r.IntN(3))
		size := uint32(0)
		if r.IntN(8) == 0 {
			opc, size = u(r, 5), u(r, 2)
		}
		return 0x5E280800 | size<<22 | opc<<12 | vreg(r)<<5 | vreg(r)
	},
	"crypto.sha512": func(r *rand.Rand) uint32 {
		switch p := r.IntN(10); {
		case p < 7: // SHA512H / H2 / SU1 / RAX1
			return 0xCE608000 | vreg(r)<<16 | u(r, 2)<<10 | vreg(r)<<5 | vreg(r)
		case p < 9: // SHA512SU0
			return 0xCEC08000 | vreg(r)<<5 | vreg(r)
		}
		// neighbours: O = 1 (SM3PARTW1/2, SM4EKEY), SM4E
		if r.IntN(2) == 0 {
			return 0xCE60C000 | vreg(r)<<16 | u(r, 2)<<10 | vreg(r)<<5 | vreg(r)
		}
		return 0xCEC08000 | u(r, 2)<<10 | vreg(r)<<5 | vreg(r)
	},
	"crypto.sha3": func(r *rand.Rand) uint32 {
		switch p := r.IntN(10); {
		case p < 6: // EOR3 / BCAX
			return 0xCE000000 | u(r, 1)<<21 | vreg(r)<<16 | vreg(r)<<10 | vreg(r)<<5 | vreg(r)
		case p < 9: // XAR
			imm6 := u(r, 6)
			if r.IntN(4) == 0 {
				imm6 = pick(r, 0, 1, 63, 32)
			}
			return 0xCE800000 | vreg(r)<<16 | imm6<<10 | vreg(r)<<5 | vreg(r)
		}
		// neighbours: Op0 = 1x (SM3SS1, unallocated)
		return 0xCE400000 | u(r, 1)<<21 | vreg(r)<<16 | vreg(r)<<10 | vreg(r)<<5 | vreg(r)
	},
	"simd.pmull": func(r *rand.Rand) uint32 {
		size := pick(r, 0, 3, 3)
		if r.IntN(8) == 0 {
			size = u(r, 2)
		}
		return 0x0E20E000 | u(r, 1)<<30 | size<<22 | vreg(r)<<16 | vreg(r)<<5 | vreg(r)
	},
	"simd.permute": func(r *rand.Rand) uint32 {
		opc := pick(r, 1, 2, 3, 5, 6, 7)
		if r.IntN(10) == 0 {
			opc = u(r, 3)
		}
		return 0x0E000800 | u(r, 1)<<30 | u(r, 2)<<22 | vreg(r)<<16 | opc<<12 | vreg(r)<<5 | vreg(r)
	},
	"simd.dupscalar": func(r *rand.Rand) uint32 {
		imm5 := u(r, 5)
		if imm5&0xf == 0 && r.IntN(4) != 0 {
			imm5 |= 1 << r.IntN(4)
		}
		op, imm4 := uint32(0), uint32(0)
		if r.IntN(10) == 0 { // neighbours: op = 1, imm4 != 0000
			op, imm4 = u(r, 1), u(r, 4)
		}
		return 0x5E000400 | op<<29 | imm5<<16 | imm4<<11 | vreg(r)<<5 | vreg(r)
	},
	"dpr.crc32": func(r *rand.Rand) uint32 {
		sf := u(r, 1)
		sz := uint32(r.IntN(3))
		if sf == 1 {
			sz = 3
		}
		if r.IntN(10) == 0 { // the UNDEFINED sf/sz combinations
			sz = u(r, 2)
		}
		return 0x1AC04000 | sf<<31 | reg(r)<<16 | u(r, 1)<<12 | sz<<10 | reg(r)<<5 | reg(r)
	},
}
