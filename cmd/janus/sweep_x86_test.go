package main

import (
	"testing"

	"golang.org/x/arch/x86/x86asm"
)

// Round N8: the amd64 sweep keeps instruction boundaries across encodings x86asm does not know
// (ADCX/ADOX, VEX: MULX, VZEROUPPER, VMOVDQU), so that a displacement field is never decoded as
// a RIP-relative LEA and turned into a spurious dynamic target, and keeps the RIP-relative
// operand of such an instruction as a data reference.
func TestSweepAmd64UnknownEncodings(t *testing.T) {
	const base = 0x401000
	code := []byte{
		0x66, 0x48, 0x0F, 0x38, 0xF6, 0xC1, // ADCX RAX, RCX
		0xF3, 0x4C, 0x0F, 0x38, 0xF6, 0xC2, // ADOX R8, RDX
		0xC4, 0xE2, 0xFB, 0xF6, 0xC3, //       MULX RAX, RAX, RBX
		0xC5, 0xFE, 0x6F, 0x05, 0x10, 0x00, 0x00, 0x00, // VMOVDQU YMM0, [rip+0x10]
		0xC5, 0xF8, 0x77, //                   VZEROUPPER
		0x48, 0x8D, 0x05, 0x20, 0x00, 0x00, 0x00, // LEA RAX, [rip+0x20]
		0x66, 0x0F, 0x3A, 0x0F, 0xC1, 0x08, // PALIGNR XMM0, XMM1, 8 (0F 3A, imm8)
		0xC3, // RET
	}
	wantLen := []int{6, 6, 5, 8, 3, 7, 6, 1}
	insts := sweepAmd64(code, base)
	if len(insts) != len(wantLen) {
		t.Fatalf("sweep found %d instructions, want %d: %+v", len(insts), len(wantLen), insts)
	}
	off := 0
	for i, in := range insts {
		if in.PC != base+uint64(off) || in.Inst.Len != wantLen[i] {
			t.Errorf("instruction %d at 0x%x len %d, want 0x%x len %d", i, in.PC, in.Inst.Len, base+uint64(off), wantLen[i])
		}
		off += wantLen[i]
	}
	if insts[5].Inst.Op != x86asm.LEA {
		t.Errorf("the LEA after the unknown encodings decodes as %v", insts[5].Inst.Op)
	}
	refs := amd64DataRefs(insts)
	want := map[uint64]string{
		base + 17 + 8 + 0x10:         "rip-mem", // VMOVDQU's operand, after its 8 bytes at offset 17
		base + 17 + 8 + 3 + 7 + 0x20: "rip-lea",
	}
	if len(refs) != len(want) {
		t.Fatalf("data references %+v, want %v", refs, want)
	}
	for _, r := range refs {
		if want[r.Target] != r.Kind {
			t.Errorf("reference %+v not expected (want %v)", r, want)
		}
	}
}

// The measured lengths of the fallback rules.
func TestFallbackLenAmd64(t *testing.T) {
	cases := []struct {
		b   []byte
		l   int
		rip bool
	}{
		{[]byte{0x66, 0x0F, 0x38, 0xF6, 0x05, 1, 0, 0, 0}, 9, true},        // ADCX EAX, [rip+1]
		{[]byte{0xF3, 0x0F, 0x38, 0xF6, 0x44, 0x24, 0x08}, 7, false},       // ADOX EAX, [rsp+8]
		{[]byte{0xC5, 0xF8, 0x77}, 3, false},                               // VZEROUPPER
		{[]byte{0xC4, 0xE3, 0x7D, 0x39, 0xC1, 0x01}, 6, false},             // VEXTRACTI128 (map 3, imm8)
		{[]byte{0x62, 0xF1, 0xFE, 0x48, 0x6F, 0x05, 0, 0, 0, 0}, 10, true}, // EVEX VMOVDQU64 [rip]
		{[]byte{0x0F, 0x0B}, 0, false},                                     // UD2: x86asm knows it; no rule
		{[]byte{0xC4, 0xE2}, 0, false},                                     // truncated
	}
	for _, c := range cases {
		l, rip, _ := fallbackLenAmd64(c.b)
		if l != c.l || rip != c.rip {
			t.Errorf("% x: len %d rip %v, want %d %v", c.b, l, rip, c.l, c.rip)
		}
	}
}
