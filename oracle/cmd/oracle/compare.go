package main

import (
	"fmt"
	"strconv"
	"strings"

	L "github.com/Giulio2002/Janus/oracle/layout"
)

// Verdicts.
const (
	Agree      = "agree"       // both succeeded with identical state, or both faulted
	Gap        = "model-gap"   // hardware succeeded, the model faulted (conservative)
	Mismatch   = "MISMATCH"    // the model succeeded with a result hardware does not produce
	Unobserved = "unobserved"  // the native run could not observe a clean outcome
	ModelError = "model-error" // janus-oracle could not parse the case
)

// Verdict is the comparison of one case.
type Verdict struct {
	ID      int      `json:"id"`
	Class   string   `json:"class"`
	Word    string   `json:"word"`
	Asm     string   `json:"asm,omitempty"`
	Verdict string   `json:"verdict"`
	Kind    string   `json:"kind"` // sub-category (fault kinds, diff kind)
	Diffs   []string `json:"diffs,omitempty"`
}

func hexv(s string) uint64 {
	v, _ := strconv.ParseUint(strings.TrimPrefix(s, "0x"), 16, 64)
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

// compareCase compares one case. A nondeterministic model result (m.Alts, the outcomes of a
// store-exclusive under every enumerated environment choice) agrees when the hardware result
// is any one of the model's outcomes: the model claims only that the machine does one of them.
// Otherwise the verdict is that of the first outcome (the all-fail stream), except that a
// hardware success no outcome reproduces is a MISMATCH even when the first outcome faulted.
func compareCase(c *L.Case, h *L.HW, m *L.Model) Verdict {
	if m == nil || len(m.Alts) == 0 {
		return compareOne(c, h, m)
	}
	first := compareOne(c, h, m)
	if first.Verdict == Agree || first.Verdict == Unobserved {
		first.Kind = "nondet/" + first.Kind
		return first
	}
	worst := first
	for i := range m.Alts {
		a := m.Alts[i]
		a.ID = m.ID
		v := compareOne(c, h, &a)
		if v.Verdict == Agree {
			v.Kind = fmt.Sprintf("nondet/alt%d/%s", i+1, v.Kind)
			return v
		}
		if v.Verdict == Mismatch && worst.Verdict != Mismatch {
			worst = v
		}
	}
	worst.Kind = "nondet/" + worst.Kind
	worst.Diffs = append(worst.Diffs, fmt.Sprintf("none of the model's %d outcomes (%d choices) matches", len(m.Alts)+1, m.Choices))
	return worst
}

func compareOne(c *L.Case, h *L.HW, m *L.Model) Verdict {
	v := Verdict{ID: c.ID, Class: c.Class, Word: c.Word}
	if h == nil || (h.Status != "ok" && h.Status != "fault" && h.Status != "selfloop") {
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
	hwPC := hexv(h.PC)
	// A branch to a misaligned target completes on hardware and faults on the next fetch
	// (PC alignment fault); the model may report that as pcMisaligned at the branch.
	hwMisalignedBranch := !hwFault && hwPC%4 != 0
	switch {
	case hwFault && m.Status == "fault":
		v.Verdict, v.Kind = Agree, "fault/"+faultName(h)+"/"+m.Fault
		return v
	case hwFault:
		v.Verdict, v.Kind = Mismatch, "model-ok-hw-fault/"+faultName(h)
		v.Diffs = []string{fmt.Sprintf("hardware %s (si_addr %s, code %d) but model succeeded (pc %s)", faultName(h), h.Addr, h.Code, m.PC)}
		return v
	case m.Status == "fault" && m.Fault == "kernel":
		// WP-C: the model leaves the result of an environment instruction to the environment
		// contract (Janus.Kernel.SiteNext): only the destination register may change (DIT: only
		// bit 24), pc + 4, and nothing else. Check the hardware against that frame.
		return compareEnv(c, h, v)
	case m.Status == "fault":
		if hwMisalignedBranch && m.Fault == "pcMisaligned" {
			v.Verdict, v.Kind = Agree, "fault/pcMisaligned"
			return v
		}
		v.Verdict, v.Kind = Gap, m.Fault
		return v
	}
	// Both succeeded: compare everything.
	for i := 0; i < 31; i++ {
		if hexv(h.X[i]) != hexv(m.X[i]) {
			v.Diffs = append(v.Diffs, fmt.Sprintf("x%d: hw %s model %s (in %s)", i, h.X[i], m.X[i], c.X[i]))
		}
	}
	if hexv(h.SP) != hexv(m.SP) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("sp: hw %s model %s (in %s)", h.SP, m.SP, c.SP))
	}
	if h.NZCV != m.NZCV {
		v.Diffs = append(v.Diffs, fmt.Sprintf("nzcv: hw %04b model %04b (in %04b)", h.NZCV, m.NZCV, c.NZCV))
	}
	if len(h.V) == 32 && len(m.V) == 32 {
		for i := 0; i < 32; i++ {
			if norm128(h.V[i]) != norm128(m.V[i]) {
				in := "0"
				if len(c.V) == 32 {
					in = c.V[i]
				}
				v.Diffs = append(v.Diffs, fmt.Sprintf("v%d: hw %s model %s (in %s)", i, h.V[i], m.V[i], in))
			}
		}
	} else if (len(h.V) == 32) != (len(m.V) == 32) {
		v.Diffs = append(v.Diffs, "v: vector registers reported by one side only")
	}
	// FPCR/FPSR: absent means 0 on either side (cases and results predating them).
	if hexv(h.FPSR) != hexv(m.FPSR) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("fpsr: hw %s model %s (in %s) [%s]", h.FPSR, m.FPSR, orZero(c.FPSR),
			fpsrDiff(hexv(h.FPSR), hexv(m.FPSR))))
	}
	if hexv(h.FPCR) != hexv(m.FPCR) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("fpcr: hw %s model %s (in %s)", h.FPCR, m.FPCR, orZero(c.FPCR)))
	}
	if hwPC != hexv(m.PC) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("pc: hw %s (pc+%d) model %s (pc+%d)", h.PC,
			int64(hwPC-L.TestPC), m.PC, int64(hexv(m.PC)-L.TestPC)))
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
			memd = append(memd, fmt.Sprintf("mem[+%d]: hw %#02x model %s", off, b, show(mm, off, c.Seed)))
		}
	}
	for off, b := range mm {
		if _, ok := hm[off]; !ok {
			memd = append(memd, fmt.Sprintf("mem[+%d]: hw %#02x (unchanged) model %#02x", off, L.Pattern(c.Seed, uint64(off)), b))
		}
	}
	if len(memd) > 0 {
		sortStrings(memd)
		if len(memd) > 8 {
			memd = append(memd[:8], fmt.Sprintf("mem: ... %d more bytes", len(memd)-8))
		}
		v.Diffs = append(v.Diffs, memd...)
	}
	if len(v.Diffs) == 0 {
		v.Verdict = Agree
		if hwMisalignedBranch {
			v.Kind = "ok/misaligned-branch"
		} else {
			v.Kind = "ok"
		}
		return v
	}
	v.Verdict = Mismatch
	var kinds []string
	for _, d := range v.Diffs {
		k := d
		if j := strings.IndexAny(d, ":["); j >= 0 {
			k = d[:j]
		} else if j := strings.IndexByte(d, ' '); j >= 0 {
			k = d[:j] // e.g. "mem: ... N more bytes" has no field separator before the text
		}
		if strings.HasPrefix(k, "x") {
			k = "reg"
		}
		if strings.HasPrefix(k, "v") {
			k = "vreg"
		}
		if len(kinds) == 0 || kinds[len(kinds)-1] != k {
			kinds = append(kinds, k)
		}
	}
	v.Kind = "state/" + strings.Join(kinds, "+")
	return v
}

// norm128 normalises a hex number of up to 128 bits (lower case, no prefix, no leading zeros).
func norm128(s string) string {
	t := strings.TrimLeft(strings.ToLower(strings.TrimPrefix(strings.TrimPrefix(s, "0x"), "0X")), "0")
	if t == "" {
		return "0"
	}
	return t
}

func show(mm map[int]int, off int, seed uint64) string {
	if b, ok := mm[off]; ok {
		return fmt.Sprintf("%#02x", b)
	}
	return fmt.Sprintf("%#02x (unchanged)", L.Pattern(seed, uint64(off)))
}

func orZero(s string) string {
	if s == "" {
		return "0"
	}
	return s
}

// fpsrDiff names the cumulative flags only one side set.
func fpsrDiff(hw, model uint64) string {
	names := map[int]string{0: "IOC", 1: "DZC", 2: "OFC", 3: "UFC", 4: "IXC", 7: "IDC", 27: "QC"}
	var out []string
	for b := 0; b < 32; b++ {
		hb, mb := hw>>b&1, model>>b&1
		if hb == mb {
			continue
		}
		n, ok := names[b]
		if !ok {
			n = fmt.Sprintf("bit%d", b)
		}
		if hb == 1 {
			out = append(out, "hw-only "+n)
		} else {
			out = append(out, "model-only "+n)
		}
	}
	return strings.Join(out, ", ")
}

// compareEnv checks a hardware result of an environment instruction (MRS of CNTVCT_EL0,
// CNTFRQ_EL0, MIDR_EL1, DIT or a feature-ID register; MSR DIT) against the frame of its environment contract: the
// destination register is the only general register that may change (MIDR_EL1: a 32-bit value;
// DIT: only bit 24), and SP, NZCV, the vector registers, FPCR/FPSR and memory are unchanged,
// with pc + 4.
func compareEnv(c *L.Case, h *L.HW, v Verdict) Verdict {
	w := uint32(hexv(c.Word))
	rt, free, mask := int(w&31), -1, ^uint64(0)
	kind := "env/msr-dit"
	switch {
	case w&0xFFFFFFE0 == 0xD53BE040:
		free, kind = rt, "env/cntvct"
	case w&0xFFFFFFE0 == 0xD53BE000:
		free, kind = rt, "env/cntfrq"
	case w&0xFFFFFFE0 == 0xD5380000:
		free, kind, mask = rt, "env/midr", 0xFFFFFFFF
	case w&0xFFFFFFE0 == 0xD53B42A0:
		free, kind, mask = rt, "env/dit", 1<<24
	case w&0xFFFFF000 == 0xD5380000 && (w>>8)&0xF >= 4 && (w>>8)&0xF <= 7:
		// the feature-ID registers: any 64-bit value (Janus.Kernel.Site.mrs (.idreg crm op2))
		free, kind = rt, "env/idreg"
	}
	for i := 0; i < 31; i++ {
		hv := hexv(h.X[i])
		if i == free {
			if hv&^mask != 0 {
				v.Diffs = append(v.Diffs, fmt.Sprintf("x%d: hw %s outside the contract's values", i, h.X[i]))
			}
			continue
		}
		if hv != hexv(c.X[i]) {
			v.Diffs = append(v.Diffs, fmt.Sprintf("x%d: hw %s changed (in %s), the contract keeps it", i, h.X[i], c.X[i]))
		}
	}
	if hexv(h.SP) != hexv(c.SP) {
		v.Diffs = append(v.Diffs, fmt.Sprintf("sp: hw %s (in %s)", h.SP, c.SP))
	}
	if h.NZCV != c.NZCV {
		v.Diffs = append(v.Diffs, fmt.Sprintf("nzcv: hw %04b (in %04b)", h.NZCV, c.NZCV))
	}
	if len(h.V) == 32 && len(c.V) == 32 {
		for i := 0; i < 32; i++ {
			if norm128(h.V[i]) != norm128(c.V[i]) {
				v.Diffs = append(v.Diffs, fmt.Sprintf("v%d changed", i))
			}
		}
	}
	if hexv(h.FPSR) != hexv(c.FPSR) || hexv(h.FPCR) != hexv(c.FPCR) {
		v.Diffs = append(v.Diffs, "fpcr/fpsr changed")
	}
	if hexv(h.PC) != L.TestPC+4 {
		v.Diffs = append(v.Diffs, fmt.Sprintf("pc: hw %s, the contract continues at pc+4", h.PC))
	}
	if len(h.Mem) != 0 {
		v.Diffs = append(v.Diffs, "mem: hw changed memory")
	}
	if len(v.Diffs) == 0 {
		v.Verdict, v.Kind = Agree, kind
		return v
	}
	v.Verdict, v.Kind = Mismatch, kind+"/frame"
	return v
}
