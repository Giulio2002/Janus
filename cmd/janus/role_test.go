package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Round 14: the report says what the STATEMENT assumes about the runtime, not what the extraction left out.
func TestRoleLines(t *testing.T) {
	join := func(r *verifiedReport) string { return strings.Join(roleLines(r), "\n") }
	// a main theorem that quantifies the allocator contract
	r := &verifiedReport{Role: "main", Contracts: []string{"runtime.newobject @ 0x1000 (pinned)"},
		ContractHyps: []string{"Janus.Contracts.NewobjectContract@runtime.newobject"}}
	s := join(r)
	if !strings.Contains(s, "Role: main theorem") || !strings.Contains(s, "Runtime contracts assumed: Janus.Contracts.NewobjectContract@runtime.newobject") {
		t.Errorf("main with a contract hypothesis: %s", s)
	}
	if strings.Contains(s, "NO contract hypothesis") {
		t.Errorf("a covered contract reported as missing: %s", s)
	}
	// the red-team finding: the extraction left runtime.newobject out, the statement assumes nothing
	r = &verifiedReport{Role: "main", Contracts: []string{"runtime.newobject @ 0x1000 (pinned)"}}
	s = join(r)
	if !strings.Contains(s, "Runtime contracts assumed: none") || !strings.Contains(s, "NO contract hypothesis in the statement: runtime.newobject") {
		t.Errorf("main without a contract hypothesis must not claim the contract: %s", s)
	}
	// a witness is labelled as such and names its main theorem
	r = &verifiedReport{Role: "witness-nonvacuous", MatchedMain: "Proof.correctness"}
	s = join(r)
	if !strings.Contains(s, "WITNESS, not a correctness claim") || !strings.Contains(s, "Proof.correctness") {
		t.Errorf("witness: %s", s)
	}
}

func TestCheckWitnessSupport(t *testing.T) {
	dir := t.TempDir()
	vd := filepath.Join(dir, verifiedDir)
	if err := os.MkdirAll(vd, 0o755); err != nil {
		t.Fatal(err)
	}
	write := func(name string) {
		if err := os.WriteFile(filepath.Join(vd, name+".json"), []byte("{}"), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	write("Proof.W.Witness.nonvacuous")
	write("Proof.Witness.nonvacuous")
	outs := []thmOutcome{
		{Theorem: "Proof.correctness", Report: &verifiedReport{Role: "main"}},
		{Theorem: "Proof.Witness.nonvacuous", Report: &verifiedReport{Role: "witness-nonvacuous", MatchedMain: "Proof.correctness"}},
		{Theorem: "Proof.W.Witness.nonvacuous", Report: &verifiedReport{Role: "witness-nonvacuous", MatchedMain: "Proof.other"}},
	}
	checkWitnessSupport(dir, outs)
	if outs[1].Err != nil || outs[1].Report == nil {
		t.Errorf("a witness for the verified main theorem must stand: %v", outs[1].Err)
	}
	if outs[2].Err == nil || outs[2].Report != nil {
		t.Errorf("a witness for a main theorem that was not verified must fail")
	}
	if _, err := os.Stat(filepath.Join(vd, "Proof.W.Witness.nonvacuous.json")); err == nil {
		t.Errorf("the withdrawn witness left its report behind")
	}
	if _, err := os.Stat(filepath.Join(vd, "Proof.Witness.nonvacuous.json")); err != nil {
		t.Errorf("the good witness's report was removed")
	}
	// witnesses alone (no main theorem in the call) are not cross-checked
	outs = []thmOutcome{{Theorem: "Proof.Witness.nonvacuous", Report: &verifiedReport{Role: "witness-nonvacuous", MatchedMain: "Proof.correctness"}}}
	checkWitnessSupport(dir, outs)
	if outs[0].Err != nil {
		t.Errorf("a lone witness must stand: %v", outs[0].Err)
	}
}
