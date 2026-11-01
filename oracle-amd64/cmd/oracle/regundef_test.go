package main

import (
	"testing"

	L "github.com/Giulio2002/Janus/oracle-amd64/layout"
)

// A register the model marks architecturally undefined (RegUndef: the destination of BSF/BSR of
// zero) is not compared; every other register still is, and an unmarked difference is a MISMATCH.
func TestRegUndefIsNotCompared(t *testing.T) {
	regs := func(r0 string) []string {
		out := make([]string, 16)
		for i := range out {
			out[i] = "0x0"
		}
		out[0] = r0
		return out
	}
	c := &L.Case{ID: 1, Class: "t", }
	h := &L.HW{Status: "ok", Regs: regs("0x1234")}
	for _, tc := range []struct {
		name     string
		regUndef int
		mRegs    []string
		want     string
	}{
		{"undefined register differs", 1, regs("0x5678"), Agree},
		{"defined register differs", 0, regs("0x5678"), Mismatch},
		{"another register differs", 1, func() []string { r := regs("0x1234"); r[3] = "0x1"; return r }(), Mismatch},
	} {
		m := &L.Model{Status: "ok", Regs: tc.mRegs, RegUndef: tc.regUndef}
		if v := compareCase(c, h, m); v.Verdict != tc.want {
			t.Errorf("%s: verdict %v, want %v (%v)", tc.name, v.Verdict, tc.want, v.Diffs)
		}
	}
}
