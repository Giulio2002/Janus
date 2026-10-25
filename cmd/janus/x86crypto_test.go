package main

import "testing"

// TestSweepADX: the x86asm sweep steps over ADCX/ADOX (which this x86asm version does not
// know) with their own length, so that it stays in step and sees the branch after them, and it
// rejects the prefix combinations the Lean decoder rejects.
func TestSweepADX(t *testing.T) {
	code := []byte{
		0x66, 0x4d, 0x0f, 0x38, 0xf6, 0xeb, // adcx r13, r11
		0xf3, 0x4d, 0x0f, 0x38, 0xf6, 0x28, // adox r13, [r8]
		0xe9, 0x10, 0x00, 0x00, 0x00, // jmp +0x10
	}
	insts := sweepAmd64(code, 0x1000)
	if len(insts) != 3 {
		t.Fatalf("swept %d instructions, want 3: %+v", len(insts), insts)
	}
	if insts[0].Inst.Len != 6 || insts[1].Inst.Len != 6 || insts[2].PC != 0x100c {
		t.Fatalf("lengths/pcs wrong: %+v", insts)
	}
	if tgt, ok := amd64BranchTarget(insts[2]); !ok || tgt != 0x100c+5+0x10 {
		t.Fatalf("branch target %#x %v", tgt, ok)
	}
	for _, b := range [][]byte{
		{0xf2, 0x0f, 0x38, 0xf6, 0xc3},       // F2: not ADX
		{0x66, 0xf3, 0x0f, 0x38, 0xf6, 0xc3}, // 66 with F3: rejected by the decoder
		{0x0f, 0x38, 0xf6, 0xc3},             // no mandatory prefix
	} {
		if _, ok := decodeADX(b); ok {
			t.Errorf("% x decoded as ADX", b)
		}
	}
}
