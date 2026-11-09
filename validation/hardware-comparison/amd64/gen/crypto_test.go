package gen

import "testing"

// ADCX/ADOX are classified and decoded with the operands and length of the instruction.
func TestADXDecode(t *testing.T) {
	for _, c := range []struct {
		b   []byte
		cls string
		n   int
		gnu string
	}{
		{[]byte{0x66, 0x48, 0x0F, 0x38, 0xF6, 0xC3}, "adcx", 6, "adcx %rbx,%rax"},
		{[]byte{0xF3, 0x0F, 0x38, 0xF6, 0x07}, "adox", 5, "adox (%rdi),%eax"},
		{[]byte{0x66, 0x4D, 0x0F, 0x38, 0xF6, 0x44, 0x24, 0x08}, "adcx", 8, "adcx 0x8(%r12,%riz),%r8"},
		{[]byte{0xF2, 0x0F, 0x38, 0xF6, 0xC3}, "invalid", 0, ""},
		{[]byte{0x66, 0xF3, 0x0F, 0x38, 0xF6, 0xC3}, "invalid", 0, ""},
		{[]byte{0x66, 0x0F, 0x38, 0xDC, 0xC1}, "aesenc", 5, ""},
		{[]byte{0x0F, 0x3A, 0xCC, 0xC1, 0x01}, "sha1rnds4", 5, ""},
	} {
		if got := Classify(c.b); got != c.cls {
			t.Errorf("% x: class %q, want %q", c.b, got, c.cls)
		}
		inst, ok := Decode(c.b)
		if c.n == 0 {
			continue
		}
		if !ok || inst.Len != c.n {
			t.Errorf("% x: len %d ok %v, want %d", c.b, inst.Len, ok, c.n)
		}
		if c.gnu != "" {
			if got := Asm(c.b); got != c.gnu {
				t.Errorf("% x: %q, want %q", c.b, got, c.gnu)
			}
		}
	}
}
