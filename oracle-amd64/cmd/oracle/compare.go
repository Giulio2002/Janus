package main

import (
	"fmt"
	"math/big"
	"strconv"
	"strings"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// Verdicts.
const (
	Agree      = "agree"       // both succeeded with identical state, or both faulted
	Gap        = "model-gap"   // hardware succeeded, the model faulted (conservative)
	Mismatch   = "MISMATCH"    // the model succeeded with a result hardware does not produce
	Unobserved = "unobserved"  // the native run could not observe a clean outcome
	ModelError = "model-error" // janus-oracle-amd64 produced no usable result
)

type Verdict struct {
	ID      int      `json:"id"`
	Class   string   `json:"class"`
	Bytes   string   `json:"bytes"`
	Asm     string   `json:"asm,omitempty"`
	Verdict string   `json:"verdict"`
	Kind    string   `json:"kind"`
	Diffs   []string `json:"diffs,omitempty"`
}

var regNames = [16]string{"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"}

func hexv(s string) uint64 {
	v, _ := strconv.ParseUint(strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X"), 16, 64)
	return v
}

func hexBig(s string) *big.Int {
	v, ok := new(big.Int).SetString(strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X"), 16)
	if !ok {
		return big.NewInt(-1)
	}
	return v
}

func faultName(h *L.HW) string {
	switch h.Sig {
	case 4:
		return "SIGILL"
	case 5:
		return "SIGTRAP"
	case 7:
		return "SIGBUS"
	case 8:
		return "SIGFPE"
	case 11:
		return "SIGSEGV"
	}
	return fmt.Sprintf("sig%d", h.Sig)
}

func flagString(f int) string {
	var b strings.Builder
	for _, x := range []struct {
		bit  int
		name byte
	}{{L.FlagOF, 'O'}, {L.FlagSF, 'S'}, {L.FlagZF, 'Z'}, {L.FlagAF, 'A'}, {L.FlagPF, 'P'}, {L.FlagCF, 'C'}} {
		if f&x.bit != 0 {
			b.WriteByte(x.name)
		} else {
			b.WriteByte('-')
		}
	}
	return b.String()
}

func compareCase(c *L.Case, h *L.HW, m *L.Model) Verdict {
	v := Verdict{ID: c.ID, Class: c.Class, Bytes: c.Bytes}
	if h == nil || (h.Status != "ok" && h.Status != "fault") {
		v.Verdict = Unobserved
		if h != nil {
			v.Kind = h.Status
		} else {
			v.Kind = "no-native-result"
		}
		return v
	}
	if m == nil || (m.Status != "ok" && m.Status != "fault") {
		v.Verdict, v.Kind = ModelError, "no-model-result"
		return v
	}
	hwFault := h.Status == "fault"
	switch {
	case hwFault && m.Status == "fault":
		v.Verdict, v.Kind = Agree, "fault/"+faultName(h)+"/"+m.Fault
		return v
	case hwFault:
		v.Verdict, v.Kind = Mismatch, "model-ok-hw-fault/"+faultName(h)
		v.Diffs = []string{fmt.Sprintf("hardware %s (si_code %d, si_addr %s) but model succeeded (pc %s, len %d)", faultName(h), h.Code, h.Addr, m.PC, m.Len)}
		return v
	case m.Status == "fault":
		v.Verdict, v.Kind = Gap, m.Fault
		return v
	}
	for i := 0; i < 16; i++ {
		if i >= len(h.Regs) || i >= len(m.Regs) {
			v.Diffs = append(v.Diffs, "regs: missing")
			break
		}
		if hexv(h.Regs[i]) != hexv(m.Regs[i]) {
			v.Diffs = append(v.Diffs, fmt.Sprintf("%s: hw %s model %s (in %s)", regNames[i], h.Regs[i], m.Regs[i], c.Regs[i]))
		}
	}
	mask := m.Defined & L.StatusFlags
	if h.RFlags&mask != m.RFlags&mask {
		v.Diffs = append(v.Diffs, fmt.Sprintf("rflags: hw %s model %s defined %s (in %s)",
			flagString(h.RFlags), flagString(m.RFlags), flagString(mask), flagString(c.RFlags)))
	}
	if h.DF != m.DF {
		v.Diffs = append(v.Diffs, fmt.Sprintf("rflags: DF hw %v model %v (in %v)", h.DF, m.DF, c.RFlags&L.FlagDF != 0))
	}
	if h.MXCSR != "" {
		in := c.MXCSR
		if in == "" {
			in = fmt.Sprintf("%#x", L.DefaultMXCSR)
		}
		switch {
		case m.MXCSR == "":
			v.Diffs = append(v.Diffs, fmt.Sprintf("mxcsr: hw %s model (missing) (in %s)", h.MXCSR, in))
		case hexv(h.MXCSR) != hexv(m.MXCSR):
			v.Diffs = append(v.Diffs, fmt.Sprintf("mxcsr: hw %s model %s (in %s) [%s vs %s]", h.MXCSR, m.MXCSR, in,
				mxcsrString(hexv(h.MXCSR)), mxcsrString(hexv(m.MXCSR))))
		}
	}
	if hexv(h.PC) != hexv(m.PC) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("pc: hw %s (pc%+d) model %s (pc%+d)", h.PC,
			int64(hexv(h.PC)-L.TestPC), m.PC, int64(hexv(m.PC)-L.TestPC)))
	}
	if len(h.XMM) == 16 {
		for i := 0; i < 16; i++ {
			if i >= len(m.XMM) {
				v.Diffs = append(v.Diffs, "xmm: missing in model")
				break
			}
			if hexBig(h.XMM[i]).Cmp(hexBig(m.XMM[i])) != 0 {
				v.Diffs = append(v.Diffs, fmt.Sprintf("xmm%d: hw %s model %s (in %s)", i, h.XMM[i], m.XMM[i], c.XMM[i]))
			}
		}
	}
	if len(h.YMMH) == 16 {
		for i := 0; i < 16; i++ {
			mv := "0x0"
			if len(m.YMMH) == 16 {
				mv = m.YMMH[i]
			}
			if hexBig(h.YMMH[i]).Cmp(hexBig(mv)) != 0 {
				in := "0x0"
				if len(c.YMMH) == 16 {
					in = c.YMMH[i]
				}
				v.Diffs = append(v.Diffs, fmt.Sprintf("ymmh%d: hw %s model %s (in %s)", i, h.YMMH[i], mv, in))
			}
		}
	} else if len(h.XMM) == 16 {
		v.Diffs = append(v.Diffs, "ymmh: not captured by the native runner")
	}
	// the AVX-512 state (WP-G): compared whenever the runner captured it (absent in the case or
	// the model = all zero)
	for _, f := range []struct {
		name       string
		hw, md, in []string
		n          int
	}{{"zmmh", h.ZMMH, m.ZMMH, c.ZMMH, 16}, {"zmmx", h.ZMMX, m.ZMMX, c.ZMMX, 16}, {"k", h.K, m.K, c.K, 8}} {
		if len(f.hw) != f.n {
			continue
		}
		for i := 0; i < f.n; i++ {
			mv, in := "0x0", "0x0"
			if len(f.md) == f.n {
				mv = f.md[i]
			}
			if len(f.in) == f.n {
				in = f.in[i]
			}
			if hexBig(f.hw[i]).Cmp(hexBig(mv)) != 0 {
				idx := i
				if f.name == "zmmx" {
					idx += 16
				}
				v.Diffs = append(v.Diffs, fmt.Sprintf("%s%d: hw %s model %s (in %s)", f.name, idx, f.hw[i], mv, in))
			}
		}
	}
	hm := map[int]int{}
	for _, e := range h.Mem {
		hm[e[0]] = e[1]
	}
	mm := map[int]int{}
	for _, e := range m.Mem {
		mm[e[0]] = e[1]
	}
	var memd []string
	for off, b := range hm {
		if mb, ok := mm[off]; !ok || mb != b {
			memd = append(memd, fmt.Sprintf("mem[+%d]: hw %#02x model %s", off, b, show(mm, off)))
		}
	}
	for off, b := range mm {
		if _, ok := hm[off]; !ok {
			memd = append(memd, fmt.Sprintf("mem[+%d]: hw (unchanged) model %#02x", off, b))
		}
	}
	if len(memd) > 0 {
		sortStrings(memd)
		if len(memd) > 8 {
			memd = append(memd[:8], fmt.Sprintf("... %d more bytes", len(memd)-8))
		}
		v.Diffs = append(v.Diffs, memd...)
	}
	if len(v.Diffs) == 0 {
		v.Verdict, v.Kind = Agree, "ok"
		return v
	}
	v.Verdict = Mismatch
	var kinds []string
	for _, d := range v.Diffs {
		k := d[:strings.IndexAny(d, ":[")]
		switch {
		case strings.HasPrefix(k, "xmm"):
			k = "xmm"
		case strings.HasPrefix(k, "ymmh"):
			k = "ymmh"
		case strings.HasPrefix(k, "zmmh"):
			k = "zmmh"
		case strings.HasPrefix(k, "zmmx"):
			k = "zmmx"
		case k == "k0" || k == "k1" || k == "k2" || k == "k3" || k == "k4" || k == "k5" || k == "k6" || k == "k7":
			k = "k"
		case k != "pc" && k != "rflags" && k != "mem" && k != "mxcsr":
			k = "reg"
		}
		if len(kinds) == 0 || kinds[len(kinds)-1] != k {
			kinds = append(kinds, k)
		}
	}
	v.Kind = "state/" + strings.Join(kinds, "+")
	return v
}

func show(mm map[int]int, off int) string {
	if b, ok := mm[off]; ok {
		return fmt.Sprintf("%#02x", b)
	}
	return "(unchanged)"
}

// mxcsrString renders MXCSR as flags/DAZ/masks/RC/FTZ, e.g. "flags=PU daz masks=IDZOUP rc=0 ftz".
func mxcsrString(m uint64) string {
	names := "IDZOUP"
	var f, k strings.Builder
	for i := 0; i < 6; i++ {
		if m>>i&1 == 1 {
			f.WriteByte(names[i])
		}
		if m>>(7+i)&1 == 1 {
			k.WriteByte(names[i])
		}
	}
	s := fmt.Sprintf("flags=%s masks=%s rc=%d", f.String(), k.String(), m>>13&3)
	if m>>6&1 == 1 {
		s += " daz"
	}
	if m>>15&1 == 1 {
		s += " ftz"
	}
	return s
}
