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
	c := &L.Case{ID: 1, Class: "t", Bytes: "480fbdc1"}
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

// regundef is accepted only for BSF/BSR (F3-less 0F BC/BD), also in a sequence; for anything else
// (TZCNT/LZCNT with F3, an ADD) it is a model error, never a hidden difference.
func TestRegUndefWhitelist(t *testing.T) {
	regs := make([]string, 16)
	for i := range regs {
		regs[i] = "0x0"
	}
	h := &L.HW{Status: "ok", Regs: regs}
	m := &L.Model{Status: "ok", Regs: regs, RegUndef: 1}
	for _, tc := range []struct {
		bytes string
		seq   []string
		want  string
	}{
		{"480fbdc1", nil, Agree},        // BSR
		{"0fbcc1", nil, Agree},          // BSF
		{"66480fbcc1", nil, Agree},      // prefixes before REX
		{"f3480fbdc1", nil, ModelError}, // LZCNT
		{"f3480fbcc1", nil, ModelError}, // TZCNT
		{"4801d8", nil, ModelError},     // ADD
		{"", []string{"4801d8", "480fbdc1"}, Agree},
		{"", []string{"4801d8", "f3480fbdc1"}, ModelError},
	} {
		c := &L.Case{ID: 1, Class: "t", Bytes: tc.bytes, Seq: tc.seq}
		if v := compareCase(c, h, m); v.Verdict != tc.want {
			t.Errorf("%q %v: verdict %v, want %v", tc.bytes, tc.seq, v.Verdict, tc.want)
		}
	}
}
