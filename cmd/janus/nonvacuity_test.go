package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func nvMain(thm string, hyps ...string) *verifiedReport {
	return &verifiedReport{Theorem: thm, Module: "P", Role: "main", ContractHyps: hyps}
}
func nvWit(thm, main, role string) *verifiedReport {
	return &verifiedReport{Theorem: thm, Module: "P", Role: role, MatchedMain: main}
}

func runNV(t *testing.T, allow bool, reps ...*verifiedReport) ([]thmOutcome, string) {
	t.Helper()
	dir := t.TempDir()
	var outs []thmOutcome
	for _, r := range reps {
		outs = append(outs, thmOutcome{Theorem: r.Theorem, Report: r})
	}
	applyNonVacuity(dir, outs, allow)
	return outs, dir
}

func TestNonVacuityContractMainWithoutWitnessFails(t *testing.T) {
	outs, dir := runNV(t, false, nvMain("P.correctness", "NewobjectContract@runtime.newobject"))
	if outs[0].Err == nil || outs[0].Report != nil {
		t.Fatalf("expected failure, got %+v", outs[0])
	}
	d := outs[0].Err.(*diag)
	if d.Stage != "non-vacuity" || !strings.Contains(d.Msg, "jointly satisfiable") || !strings.Contains(d.Next, "example") {
		t.Errorf("diag: %+v", d)
	}
	if _, err := os.Stat(filepath.Join(dir, "verified.json")); err == nil {
		t.Error("report not withdrawn")
	}
}

func TestNonVacuityMatchingWitnessPasses(t *testing.T) {
	outs, dir := runNV(t, false, nvMain("P.correctness", "C@f"), nvWit("P.Witness.nonvacuous", "P.correctness", "witness-nonvacuous"), nvWit("P.Witness.returns", "P.correctness", "witness-returns"))
	for _, o := range outs {
		if o.Err != nil {
			t.Fatalf("%s: %v", o.Theorem, o.Err)
		}
	}
	r := outs[0].Report
	if r.NonVacuity != nvShown || r.NonVacuityWitness != "P.Witness.nonvacuous" || r.NonVacuityReturns != "P.Witness.returns" {
		t.Errorf("%+v", r)
	}
	if !strings.Contains(nonVacuityLine(r), "shown by P.Witness.nonvacuous") {
		t.Error(nonVacuityLine(r))
	}
	b, _ := os.ReadFile(filepath.Join(dir, "verified", "P.correctness.json"))
	var back verifiedReport
	if json.Unmarshal(b, &back) != nil || back.NonVacuity != nvShown {
		t.Errorf("json: %s", b)
	}
	if outs[1].Report.NonVacuity != nvWitness {
		t.Error("witness status")
	}
}

func TestNonVacuityWrongOrReturnsOnlyWitnessFails(t *testing.T) {
	// a witness for a DIFFERENT theorem
	outs, _ := runNV(t, false, nvMain("P.correctness", "C@f"), nvMain("P.other"), nvWit("P.Witness.nonvacuous", "P.other", "witness-nonvacuous"))
	if outs[0].Err == nil {
		t.Error("witness of another theorem accepted")
	}
	if outs[1].Err != nil || outs[1].Report.NonVacuity != nvShown {
		t.Error("the other theorem should be shown")
	}
	// the witness of another module
	w := nvWit("Q.Witness.nonvacuous", "P.correctness", "witness-nonvacuous")
	w.Module = "Q"
	outs, _ = runNV(t, false, nvMain("P.correctness", "C@f"), w)
	if outs[0].Err == nil {
		t.Error("witness of another module accepted")
	}
	// only a returns witness: not enough
	outs, _ = runNV(t, false, nvMain("P.correctness", "C@f"), nvWit("P.Witness.returns", "P.correctness", "witness-returns"))
	if outs[0].Err == nil || !strings.Contains(outs[0].Err.(*diag).Msg, "does not show non-vacuity") {
		t.Errorf("returns-only: %+v", outs[0].Err)
	}
}

func TestNonVacuityAuditOnlyAndNoContract(t *testing.T) {
	outs, dir := runNV(t, true, nvMain("P.correctness", "C@f"))
	r := outs[0].Report
	if outs[0].Err != nil || r.NonVacuity != nvAuditOnly || !strings.Contains(nonVacuityLine(r), "NOT a verification") {
		t.Errorf("audit-only: %+v", outs[0])
	}
	// audit-only is not a verification: no report a consumer could take for one
	if _, err := os.Stat(filepath.Join(dir, "verified.json")); err == nil {
		t.Error("audit-only left a verified.json")
	}
	// UP3c: a contract-free main theorem without a verified witness is refused too (no bypass)
	outs, _ = runNV(t, false, nvMain("P.correctness"))
	if outs[0].Err == nil || !strings.Contains(outs[0].Err.Error(), "no kernel-checked non-vacuity witness") {
		t.Errorf("contract-free main without witness accepted: %+v", outs[0])
	}
	outs, _ = runNV(t, false, nvMain("P.correctness"), nvWit("P.Witness.nonvacuous", "P.correctness", "witness-nonvacuous"))
	if outs[0].Err != nil || outs[0].Report.NonVacuity != nvShown {
		t.Errorf("contract-free main with a witness refused: %+v", outs[0])
	}
}

func TestNonVacuitySingleAndBatch(t *testing.T) {
	dir := t.TempDir()
	if err := nonVacuitySingle(dir, nvMain("P.correctness", "C@f"), false); err == nil {
		t.Error("single contract main without witness accepted")
	}
	r := nvMain("P.correctness", "C@f")
	if err := nonVacuitySingle(dir, r, true); err != nil || r.NonVacuity != nvAuditOnly {
		t.Error("single audit-only")
	}
	if _, err := os.Stat(filepath.Join(dir, "verified.json")); err == nil {
		t.Error("single audit-only left a verified.json")
	}
	m := &consumerRequest{Report: nvMain("P.correctness", "C@f")}
	w := &consumerRequest{Report: nvWit("P.Witness.nonvacuous", "P.correctness", "witness-nonvacuous")}
	nonVacuityBatch([]*consumerRequest{m, w}, false)
	if m.Err != nil || m.Report.NonVacuity != nvShown {
		t.Error("batch with witness")
	}
	m2 := &consumerRequest{Report: nvMain("P.correctness", "C@f")}
	nonVacuityBatch([]*consumerRequest{m2}, false)
	if m2.Err == nil {
		t.Error("batch without witness")
	}
}

func TestNonVacuityMatchedMains(t *testing.T) {
	// one witness serving two main theorems (a precondition they share)
	w := nvWit("P.Witness.nonvacuous", "P.correctness", "witness-nonvacuous")
	w.MatchedMains = []string{"P.correctness", "P.full_write"}
	outs, _ := runNV(t, false, nvMain("P.correctness", "C@f"), nvMain("P.full_write", "C@f"), w)
	for _, o := range outs {
		if o.Err != nil {
			t.Fatalf("%s: %v", o.Theorem, o.Err)
		}
	}
	if outs[1].Report.NonVacuity != nvShown || outs[1].Report.NonVacuityWitness != "P.Witness.nonvacuous" {
		t.Errorf("second main: %+v", outs[1].Report)
	}
	// a third main the witness does not serve is rejected
	outs, _ = runNV(t, false, nvMain("P.correctness", "C@f"), nvMain("P.third", "C@f"), w)
	if outs[0].Err != nil || outs[1].Err == nil {
		t.Errorf("correctness ok, third rejected: %v / %v", outs[0].Err, outs[1].Err)
	}
	// checkWitnessSupport keeps a witness that supports any verified main
	mains := map[string]bool{"P.full_write": true}
	if !witnessSupportsAny(w, mains) || witnessSupportsAny(w, map[string]bool{"P.third": true}) {
		t.Error("witnessSupportsAny")
	}
}

// UP3: --allow-no-witness never reaches the policy (only --audit-only does), so no flag turns a contract-assuming theorem
// without a verified Witness.nonvacuous into a verified one; a rejection says so.
func TestAllowNoWitnessIsInert(t *testing.T) {
	for _, f := range []string{"verify.go", "batch.go"} {
		b, err := os.ReadFile(f)
		if err != nil {
			t.Fatal(err)
		}
		src := string(b)
		for _, bad := range []string{`flags["allow-no-witness"]`, `opts["allow-no-witness"]`} {
			if strings.Contains(src, bad) {
				t.Errorf("%s reads the allow-no-witness flag (%s): it must stay inert", f, bad)
			}
		}
	}
	_, _, _, d := nonVacuityVerdict(nvMain("P.correctness", "C@f"), nil, false)
	if d == nil || !strings.Contains(d.Msg, "does not bypass") {
		t.Errorf("rejection must say the flag does not bypass: %+v", d)
	}
}
