package main

import (
	"reflect"
	"testing"
)

// TestCallerSlots: the `caller` argument of a stack-growth statement is found in the printed statement (it is disclosed by the report).
func TestCallerSlots(t *testing.T) {
	for _, c := range []struct {
		stmt string
		want []string
	}{
		{"Proof.e10 (reloc : S → S → Prop) : Janus.Contracts.Stack.EnsuresGrow Extracted.program reloc Extracted.entry [] (fun x => True) (fun s => BitVec.toNat (s.regs 30) = 0 ∧ False) fun x x_1 => True",
			[]string{"(fun s => BitVec.toNat (s.regs 30) = 0 ∧ False)"}},
		{"Proof.d9 : Janus.Contracts.StackAmd64.EnsuresGrow64 Extracted.program reloc Extracted.entry [x, y] (fun s => P s) (GCaller FT hi fs) fun _ s' => s'.regs 0 = x",
			[]string{"(GCaller FT hi fs)"}},
		{"Proof.correctness : Janus.GoABI.Ensures Extracted.program Extracted.entry [] pre post", nil},
	} {
		got := callerSlots(c.stmt)
		if !reflect.DeepEqual(got, c.want) {
			t.Errorf("callerSlots(%q) = %q, want %q", c.stmt, got, c.want)
		}
	}
}
