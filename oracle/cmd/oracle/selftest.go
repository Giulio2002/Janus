package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/Giulio2002/Janus/oracle/gen"
	L "github.com/Giulio2002/Janus/oracle/layout"
)

// cmdSelftest checks the native harness (not the model) against hand-computed results, so
// a broken trampoline cannot masquerade as agreement or disagreement.
func cmdSelftest(args []string) {
	fs := flag.NewFlagSet("selftest", flag.ExitOnError)
	var o runOpts
	fs.StringVar(&o.qemu, "qemu", "/usr/bin/qemu-aarch64", "qemu-aarch64 (empty: run natively)")
	fs.StringVar(&o.runner, "runner", "oracle/bin/runner", "native runner")
	fs.IntVar(&gen.DCZID, "dczid", gen.DCZID, "DCZID_EL0 of the reference machine (runner -dczid)")
	fs.Parse(args)

	type tc struct {
		name  string
		word  uint32
		setup func(*gen.State)
		check func(c *L.Case, h *L.HW) string
	}
	T := uint64(L.TestPC)
	D := uint64(L.DataBase)
	x := func(h *L.HW, i int) uint64 { return hexv(h.X[i]) }
	expect := func(status string, pc uint64) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			if h.Status != status || hexv(h.PC) != pc {
				return fmt.Sprintf("want %s pc %#x, got %s pc %s sig %d", status, pc, h.Status, h.PC, h.Sig)
			}
			return ""
		}
	}
	and := func(fs ...func(c *L.Case, h *L.HW) string) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			for _, f := range fs {
				if e := f(c, h); e != "" {
					return e
				}
			}
			return ""
		}
	}
	reg := func(i int, v uint64) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			if x(h, i) != v {
				return fmt.Sprintf("x%d = %s, want %#x", i, h.X[i], v)
			}
			return ""
		}
	}
	preserved := func(except ...int) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			skip := map[int]bool{}
			for _, e := range except {
				skip[e] = true
			}
			for i := 0; i < 31; i++ {
				if !skip[i] && hexv(h.X[i]) != hexv(c.X[i]) {
					return fmt.Sprintf("x%d changed: %s -> %s", i, c.X[i], h.X[i])
				}
			}
			if !skip[31] && hexv(h.SP) != hexv(c.SP) {
				return "sp changed"
			}
			if !skip[32] && h.NZCV != c.NZCV {
				return fmt.Sprintf("nzcv changed %04b -> %04b", c.NZCV, h.NZCV)
			}
			if !skip[33] && len(h.Mem) != 0 {
				return "memory changed"
			}
			return ""
		}
	}
	tests := []tc{
		{"add x0, x1, #1", 0x91000420, func(s *gen.State) { s.X[1] = 5 }, and(expect("ok", T+4), reg(0, 6), preserved(0))},
		{"udf #0", 0, nil, and(expect("fault", T), func(c *L.Case, h *L.HW) string {
			if h.Sig != 4 {
				return "want SIGILL"
			}
			return ""
		}, preserved())},
		{"str x0, [x1]", 0xf9000020, func(s *gen.State) { s.X[0] = 0x1122334455667788; s.X[1] = D + 64; s.Seed = 0 },
			and(expect("ok", T+4), preserved(33), func(c *L.Case, h *L.HW) string {
				want := map[int]int{64: 0x88, 65: 0x77, 66: 0x66, 67: 0x55, 68: 0x44, 69: 0x33, 70: 0x22, 71: 0x11}
				for off, b := range want {
					if int(L.Pattern(0, uint64(off))) == b {
						delete(want, off)
					}
				}
				if len(h.Mem) != len(want) {
					return fmt.Sprintf("mem diff %v", h.Mem)
				}
				for _, e := range h.Mem {
					if want[e[0]] != e[1] {
						return fmt.Sprintf("mem diff %v", h.Mem)
					}
				}
				return ""
			})},
		{"ldr x0, [x1, #8]", 0xf9400420, func(s *gen.State) { s.X[1] = D + 256; s.Seed = 7 },
			and(expect("ok", T+4), preserved(0), func(c *L.Case, h *L.HW) string {
				var v uint64
				for k := 7; k >= 0; k-- {
					v = v<<8 | uint64(L.Pattern(7, uint64(264+k)))
				}
				return reg(0, v)(c, h)
			})},
		{"ldr x0, [x2] (unmapped)", 0xf9400040, func(s *gen.State) { s.X[2] = 0x2220 }, and(expect("fault", T), preserved())},
		{"ldr x0, [x2] (guard below buffer)", 0xf9400040, func(s *gen.State) { s.X[2] = D - 8 }, and(expect("fault", T), preserved())},
		{"ldr x0, [x2] (straddles buffer end)", 0xf9400040, func(s *gen.State) { s.X[2] = D + L.DataSize - 4 }, and(expect("fault", T), preserved())},
		{"b #+8", 0x14000002, nil, and(expect("ok", T+8), preserved())},
		{"b . (self loop)", 0x14000000, nil, and(expect("selfloop", T), preserved())},
		{"bl #-16", 0x97fffffc, nil, and(expect("ok", T-16), reg(30, T+4), preserved(30))},
		{"blr x1", 0xd63f0020, func(s *gen.State) { s.X[1] = T + 0x100 }, and(expect("ok", T+0x100), reg(30, T+4), preserved(30))},
		{"br x1 (far, unmapped)", 0xd61f0020, func(s *gen.State) { s.X[1] = 0x7700_0000_0000 }, and(expect("ok", 0x7700_0000_0000), preserved())},
		{"br x1 (into data buffer, not executable)", 0xd61f0020, func(s *gen.State) { s.X[1] = D + 16 }, and(expect("ok", D+16), preserved())},
		{"adds x0, x1, x1", 0xab010020, func(s *gen.State) { s.X[1] = 1 << 63; s.NZCV = 8 }, and(expect("ok", T+4), reg(0, 0), preserved(0, 32),
			func(c *L.Case, h *L.HW) string {
				if h.NZCV != 0b0111 {
					return fmt.Sprintf("nzcv %04b", h.NZCV)
				}
				return ""
			})},
		{"mov sp, x1", 0x9100003f, func(s *gen.State) { s.X[1] = D + 0x330 }, and(expect("ok", T+4), preserved(31), func(c *L.Case, h *L.HW) string {
			if hexv(h.SP) != D+0x330 {
				return "sp " + h.SP
			}
			return ""
		})},
	}
	// Vector registers and TPIDR_EL0: loaded from the case, captured from the signal frame.
	vin := func(c *L.Case, i int) string {
		if len(c.V) != 32 {
			return "0"
		}
		return c.V[i]
	}
	vreg := func(i int, want func(c *L.Case) string) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			if len(h.V) != 32 {
				return "no vector registers reported"
			}
			if w := want(c); norm128(h.V[i]) != norm128(w) {
				return fmt.Sprintf("v%d = %s, want %s", i, h.V[i], w)
			}
			return ""
		}
	}
	vpreserved := func(except ...int) func(c *L.Case, h *L.HW) string {
		return func(c *L.Case, h *L.HW) string {
			skip := map[int]bool{}
			for _, e := range except {
				skip[e] = true
			}
			if len(h.V) != 32 {
				return "no vector registers reported"
			}
			for i := 0; i < 32; i++ {
				if !skip[i] && norm128(h.V[i]) != norm128(vin(c, i)) {
					return fmt.Sprintf("v%d changed: %s -> %s", i, vin(c, i), h.V[i])
				}
			}
			return ""
		}
	}
	setV := func(s *gen.State) {
		for i := range s.V {
			s.V[i] = [2]uint64{0x0101010101010101 * uint64(i+1), 0x1111111111111111*uint64(i%15+1) ^ 0x8000000000000000}
		}
		s.TPIDR = 0x123456789abcdef0
	}
	tests = append(tests,
		tc{"nop (vector registers preserved)", 0xd503201f, setV, and(expect("ok", T+4), preserved(), vpreserved())},
		tc{"mov v0.16b, v1.16b", 0x4ea11c20, setV, and(expect("ok", T+4), preserved(), vpreserved(0),
			vreg(0, func(c *L.Case) string { return c.V[1] }))},
		tc{"umov x0, v1.d[1]", 0x4e183c20, setV, and(expect("ok", T+4), preserved(0), vpreserved(),
			reg(0, 0x2222222222222222^0x8000000000000000))},
		tc{"dup v2.16b, w3", 0x4e010c62, func(s *gen.State) { setV(s); s.X[3] = 0x1234567890abcdef }, and(expect("ok", T+4),
			preserved(), vpreserved(2), vreg(2, func(c *L.Case) string { return "0xefefefefefefefefefefefefefefefef" }))},
		tc{"ldr q0, [x1]", 0x3dc00020, func(s *gen.State) { setV(s); s.X[1] = D + 512; s.Seed = 5 },
			and(expect("ok", T+4), preserved(), vpreserved(0), vreg(0, func(c *L.Case) string {
				var lo, hi uint64
				for k := 7; k >= 0; k-- {
					lo = lo<<8 | uint64(L.Pattern(5, uint64(512+k)))
					hi = hi<<8 | uint64(L.Pattern(5, uint64(520+k)))
				}
				return fmt.Sprintf("0x%x%016x", hi, lo)
			}))},
		tc{"mrs x0, tpidr_el0", 0xd53bd040, setV, and(expect("ok", T+4), preserved(0), vpreserved(), reg(0, 0x123456789abcdef0))},
	)
	// nop under every NZCV, all registers distinct: the trampoline must preserve everything.
	for f := 0; f < 16; f++ {
		f := f
		tests = append(tests, tc{fmt.Sprintf("nop nzcv=%04b", f), 0xd503201f, func(s *gen.State) {
			for i := range s.X {
				s.X[i] = 0x0101010101010101*uint64(i+1) ^ uint64(f)<<40
			}
			s.NZCV = f
		}, and(expect("ok", T+4), preserved())})
	}
	var cases []L.Case
	for i, t := range tests {
		var s gen.State
		for r := range s.X {
			s.X[r] = 0x1000 + uint64(r)
		}
		s.SP = D + 2048
		s.Seed = 3
		if t.setup != nil {
			t.setup(&s)
		}
		cases = append(cases, gen.Case(i, "selftest", t.word, s))
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
			msg = t.check(&cases[i], h)
		}
		if msg != "" {
			fail++
			fmt.Printf("FAIL %-40s %s\n", t.name, msg)
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
