package main

import (
	"encoding/hex"
	"flag"
	"fmt"
	"os"

	"github.com/Giulio2002/Janus/oracle-amd64/gen"
	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// cmdSelftest checks the native harness (not the model) against hand-computed results, so
// a broken trampoline cannot masquerade as agreement or disagreement.
func cmdSelftest(args []string) {
	fs := flag.NewFlagSet("selftest", flag.ExitOnError)
	var o runOpts
	fs.StringVar(&o.runner, "runner", "oracle-amd64/bin/runner", "native runner")
	fs.Parse(args)

	type check func(c *L.Case, h *L.HW) string
	type tc struct {
		name  string
		bytes string
		setup func(*gen.State)
		check check
	}
	T := uint64(L.TestPC)
	D := uint64(L.DataBase)
	reg := func(h *L.HW, i int) uint64 { return hexv(h.Regs[i]) }
	expect := func(status string, pc uint64) check {
		return func(c *L.Case, h *L.HW) string {
			if h.Status != status || hexv(h.PC) != pc {
				return fmt.Sprintf("want %s pc %#x, got %s pc %s sig %d code %d", status, pc, h.Status, h.PC, h.Sig, h.Code)
			}
			return ""
		}
	}
	fault := func(sig int) check {
		return func(c *L.Case, h *L.HW) string {
			if h.Status != "fault" || h.Sig != sig {
				return fmt.Sprintf("want fault sig %d, got %s sig %d pc %s", sig, h.Status, h.Sig, h.PC)
			}
			return ""
		}
	}
	and := func(fs ...check) check {
		return func(c *L.Case, h *L.HW) string {
			for _, f := range fs {
				if e := f(c, h); e != "" {
					return e
				}
			}
			return ""
		}
	}
	r := func(i int, v uint64) check {
		return func(c *L.Case, h *L.HW) string {
			if reg(h, i) != v {
				return fmt.Sprintf("%s = %s, want %#x", regNames[i], h.Regs[i], v)
			}
			return ""
		}
	}
	flags := func(f int) check {
		return func(c *L.Case, h *L.HW) string {
			if h.RFlags != f {
				return fmt.Sprintf("rflags %s, want %s", flagString(h.RFlags), flagString(f))
			}
			return ""
		}
	}
	xmm := func(i int, v string) check {
		return func(c *L.Case, h *L.HW) string {
			if len(h.XMM) != 16 || hexBig(h.XMM[i]).Cmp(hexBig(v)) != 0 {
				return fmt.Sprintf("xmm%d = %v, want %s", i, h.XMM, v)
			}
			return ""
		}
	}
	mem := func(want map[int]int) check {
		return func(c *L.Case, h *L.HW) string {
			init := map[int]int{}
			for _, e := range c.Init {
				init[e[0]] = e[1]
			}
			w := map[int]int{}
			for off, b := range want {
				old := int(L.Pattern(c.Seed, uint64(off)))
				if v, ok := init[off]; ok {
					old = v
				}
				if old != b {
					w[off] = b
				}
			}
			if len(h.Mem) != len(w) {
				return fmt.Sprintf("mem diff %v, want %v", h.Mem, w)
			}
			for _, e := range h.Mem {
				if w[e[0]] != e[1] {
					return fmt.Sprintf("mem diff %v, want %v", h.Mem, w)
				}
			}
			return ""
		}
	}
	preserved := func(except ...string) check {
		return func(c *L.Case, h *L.HW) string {
			skip := map[string]bool{}
			for _, e := range except {
				skip[e] = true
			}
			for i := 0; i < 16; i++ {
				if !skip[regNames[i]] && hexv(h.Regs[i]) != hexv(c.Regs[i]) {
					return fmt.Sprintf("%s changed: %s -> %s", regNames[i], c.Regs[i], h.Regs[i])
				}
			}
			if !skip["flags"] && h.RFlags != c.RFlags {
				return fmt.Sprintf("rflags changed %s -> %s", flagString(c.RFlags), flagString(h.RFlags))
			}
			if !skip["xmm"] {
				if len(h.XMM) != 16 {
					return "no xmm captured"
				}
				for i := 0; i < 16; i++ {
					if hexBig(h.XMM[i]).Cmp(hexBig(c.XMM[i])) != 0 {
						return fmt.Sprintf("xmm%d changed %s -> %s", i, c.XMM[i], h.XMM[i])
					}
				}
			}
			if !skip["mem"] && len(h.Mem) != 0 {
				return "memory changed"
			}
			return ""
		}
	}
	le := func(off int, v uint64, n int) map[int]int {
		m := map[int]int{}
		for k := 0; k < n; k++ {
			m[off+k] = int(v >> (8 * k) & 0xff)
		}
		return m
	}
	plant := func(s *gen.State, off int, v uint64) {
		for k := 0; k < 8; k++ {
			s.Init = append(s.Init, [2]int{off + k, int(v >> (8 * k) & 0xff)})
		}
	}
	tests := []tc{
		{"add rax, rbx", "4801d8", func(s *gen.State) { s.Regs[0], s.Regs[3] = 5, 7 },
			and(expect("ok", T+3), r(0, 12), flags(L.FlagPF), preserved("rax", "flags"))},
		{"adc rax, rbx (CF=1, wraps)", "4811d8", func(s *gen.State) { s.Regs[0], s.Regs[3], s.RFlags = ^uint64(0), 0, L.FlagCF },
			and(expect("ok", T+3), r(0, 0), flags(L.FlagCF|L.FlagZF|L.FlagPF|L.FlagAF), preserved("rax", "flags"))},
		{"sub rax, rbx (borrow)", "4829d8", func(s *gen.State) { s.Regs[0], s.Regs[3] = 1, 2 },
			and(expect("ok", T+3), r(0, ^uint64(0)), flags(L.FlagCF|L.FlagSF|L.FlagPF|L.FlagAF), preserved("rax", "flags"))},
		{"add eax, ebx (overflow, zero-extends)", "01d8", func(s *gen.State) { s.Regs[0], s.Regs[3] = 0xffffffff7fffffff, 1 },
			and(expect("ok", T+2), r(0, 0x80000000), flags(L.FlagOF|L.FlagSF|L.FlagAF|L.FlagPF), preserved("rax", "flags"))},
		{"mov rax, [rbx+8]", "488b4308", func(s *gen.State) { s.Regs[3], s.Seed = D+256, 7 },
			and(expect("ok", T+4), preserved("rax"), func(c *L.Case, h *L.HW) string {
				var v uint64
				for k := 7; k >= 0; k-- {
					v = v<<8 | uint64(L.Pattern(7, uint64(264+k)))
				}
				return r(0, v)(c, h)
			})},
		{"mov [rbx], rax", "488903", func(s *gen.State) { s.Regs[0], s.Regs[3], s.Seed = 0x1122334455667788, D+64, 0 },
			and(expect("ok", T+3), preserved("mem"), mem(le(64, 0x1122334455667788, 8)))},
		{"push rax", "50", func(s *gen.State) { s.Regs[0] = 0xdeadbeefcafef00d },
			and(expect("ok", T+1), r(4, D+2040), preserved("rsp", "mem"), mem(le(2040, 0xdeadbeefcafef00d, 8)))},
		{"pop rcx", "59", func(s *gen.State) { plant(s, 2048, 0x0123456789abcdef) },
			and(expect("ok", T+1), r(1, 0x0123456789abcdef), r(4, D+2056), preserved("rcx", "rsp"))},
		{"call +0x10", "e810000000", nil,
			and(expect("ok", T+0x15), r(4, D+2040), preserved("rsp", "mem"), mem(le(2040, T+5, 8)))},
		{"ret (to code page)", "c3", func(s *gen.State) { plant(s, 2048, T+0x40) },
			and(expect("ok", T+0x40), r(4, D+2056), preserved("rsp"))},
		{"ret (non-canonical: #GP at ret)", "c3", func(s *gen.State) { plant(s, 2048, 0x8000_0000_0000_0000) },
			and(fault(11), preserved())},
		{"jmp +0x10", "eb10", nil, and(expect("ok", T+0x12), preserved())},
		{"jne +0x10 (taken)", "7510", nil, and(expect("ok", T+0x12), preserved())},
		{"jne +0x10 (not taken)", "7510", func(s *gen.State) { s.RFlags = L.FlagZF }, and(expect("ok", T+2), preserved())},
		{"jmp . (self)", "ebfe", nil, and(expect("ok", T), preserved())},
		{"jmp rax (far, unmapped)", "ffe0", func(s *gen.State) { s.Regs[0] = 0x7700_0000_0000 }, and(expect("ok", 0x7700_0000_0000), preserved())},
		{"jmp rax (data buffer, not executable)", "ffe0", func(s *gen.State) { s.Regs[0] = D + 16 }, and(expect("ok", D+16), preserved())},
		{"jmp rax (non-canonical)", "ffe0", func(s *gen.State) { s.Regs[0] = 0x0100_0000_0000_0000 }, and(fault(11), preserved())},
		{"mov rax, [rbx] (unmapped)", "488b03", func(s *gen.State) { s.Regs[3] = 0x2220 }, and(fault(11), preserved())},
		{"mov rax, [rbx] (guard below buffer)", "488b03", func(s *gen.State) { s.Regs[3] = D - 8 }, and(fault(11), preserved())},
		{"mov rax, [rbx] (straddles buffer end)", "488b03", func(s *gen.State) { s.Regs[3] = D + L.DataSize - 4 }, and(fault(11), preserved())},
		{"div rbx (by zero)", "48f7f3", func(s *gen.State) { s.Regs[3] = 0 }, and(fault(8), preserved())},
		{"ud2", "0f0b", nil, and(fault(4), preserved())},
		{"int3", "cc", nil, and(fault(5), preserved())},
		{"movups xmm0, [rbx]", "0f1003", func(s *gen.State) { s.Regs[3], s.Seed = D+16, 0 },
			and(expect("ok", T+3), preserved("xmm"), func(c *L.Case, h *L.HW) string {
				v := ""
				for k := 15; k >= 0; k-- {
					v += fmt.Sprintf("%02x", L.Pattern(0, uint64(16+k)))
				}
				return xmm(0, "0x"+v)(c, h)
			})},
		{"xorps xmm1, xmm1", "0f57c9", func(s *gen.State) { s.XMM[1] = [2]uint64{0x1234, 0x5678} },
			and(expect("ok", T+3), xmm(1, "0x0"), preserved("xmm"))},
		{"movups [rbx], xmm15", "440f113b", func(s *gen.State) {
			s.Regs[3], s.Seed, s.XMM[15] = D+128, 0, [2]uint64{0x0807060504030201, 0x100f0e0d0c0b0a09}
		}, and(expect("ok", T+4), preserved("mem"), func(c *L.Case, h *L.HW) string {
			m := le(128, 0x0807060504030201, 8)
			for k, v := range le(136, 0x100f0e0d0c0b0a09, 8) {
				m[k] = v
			}
			return mem(m)(c, h)
		})},
	}
	for f := 0; f < 64; f++ {
		f := f
		tests = append(tests, tc{fmt.Sprintf("nop flags=%s", flagString(gen.FlagCombo(f))), "90", func(s *gen.State) {
			for i := range s.Regs {
				if i != 4 {
					s.Regs[i] = 0x0101010101010101*uint64(i+1) ^ uint64(f)<<40
				}
			}
			for i := range s.XMM {
				s.XMM[i] = [2]uint64{uint64(i)*0x1111 + uint64(f), ^uint64(i)}
			}
			s.RFlags = gen.FlagCombo(f)
		}, and(expect("ok", T+1), preserved())})
	}
	var cases []L.Case
	for i, t := range tests {
		var s gen.State
		for k := range s.Regs {
			s.Regs[k] = 0x1000 + uint64(k)
		}
		s.Regs[4] = D + 2048
		s.Seed = 3
		if t.setup != nil {
			t.setup(&s)
		}
		b, _ := hex.DecodeString(t.bytes)
		cases = append(cases, gen.Case(i, "selftest", b, s))
	}
	hw := runNative(o, cases)
	fail := 0
	for i, t := range tests {
		var h *L.HW
		for j := range hw {
			if hw[j].ID == i {
				h = &hw[j]
			}
		}
		msg := "no result"
		if h != nil {
			if h.Status == "error" {
				msg = "runner error: " + h.Note
			} else {
				msg = t.check(&cases[i], h)
			}
		}
		if msg != "" {
			fail++
			fmt.Printf("FAIL %-44s %s\n", t.name, msg)
		} else {
			fmt.Printf("ok   %s\n", t.name)
		}
	}
	if fail > 0 {
		fmt.Printf("%d/%d harness self-tests failed\n", fail, len(tests))
		os.Exit(1)
	}
	fmt.Printf("all %d harness self-tests passed\n", len(tests))
}
