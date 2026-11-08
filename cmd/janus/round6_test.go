package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// Round 6 F1/F2 (docs/AUDIT-ROUND6.md): a proof-local name with lookalike letters
// (`Εxtracted.program`, `Janus.GoABI.Εnsures`) or a `«Extracted.program»` component prints like
// the trusted constant it imitates, and an out-of-range numeral (`18446744073709551616` at
// `BitVec 64`) reads as a value it is not. All must be rejected at the statement-identity stage;
// in-range numerals stay accepted.
func TestRound6StatementNames(t *testing.T) {
	defer parallel(t)()
	needLean(t)
	useTestCache(t)
	if _, err := detectSandbox(false); err != nil {
		t.Skipf("no sandbox available: %v", err)
	}
	add := mustExtract(t, "example.com/basic.Add")
	for a, want := range map[string]string{
		"F1a_homoglyph_extracted_program": "shadows the Extracted namespace",
		"F1b_guillemet_extracted":         "shadows the Extracted namespace",
		"F1c_homoglyph_ensures":           "lookalike letters",
		"F2b_wrapped_numeral_def":         "out-of-range numeral",
	} {
		p := filepath.Join(repoRoot, "audit", "round6", "attacks", a+".lean")
		code, _, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot)
		if code != 1 || !strings.Contains(stderr, want) || !strings.Contains(stderr, "Stage: statement identity") {
			t.Errorf("%s not rejected (%q): %d %s", a, want, code, stderr)
		}
	}
	// The control is verified together with a tied witness (a main theorem is verified only with one): the attack file
	// plus the concrete call Add(3, 4).
	src, err := os.ReadFile(filepath.Join(repoRoot, "audit", "round6", "attacks", "F2c_numeral_in_range.lean"))
	if err != nil {
		t.Fatal(err)
	}
	p := writeProof(t, withAddWitness(t, string(src), "", "", "True", "s'.regs 0 = x + y ∧ (18446744073709551615 : BitVec 64) ≠ 0 ∧ (255 : UInt8) ≠ 0", "trivial"))
	if code, out, stderr := runJanus(t, "verify", add, "--proof", p, "--janus-root", repoRoot,
		"--theorem", "Proof.correctness", "--theorem", "Proof.Witness.nonvacuous"); code != 0 {
		t.Errorf("F2c (in-range numerals) no longer verifies: %s\n%s", out, stderr)
	}
}

// withAddWitness appends to an honest arm64 Add control (`namespace Proof ... end Proof`, correctness taking x y [after
// the extra arguments passed to it, `args`]) a Witness.nonvacuous at the concrete call Add(3, 4). binder is an extra
// existential binder (`(inst : ...)`, or ""), inst its value (or ""), pre the precondition conjunct, post the
// postcondition in x y s', proof the proof of pre (also passed to correctness as its hypothesis when binder is set).
func withAddWitness(t *testing.T, src, binder, inst, pre, post, proof string) string {
	t.Helper()
	if !strings.HasSuffix(src, "end Proof\n") {
		t.Fatal("control does not end with `end Proof`")
	}
	args, exInst, hyp := "", "", ""
	if binder != "" { // the control states a hypothesis (pre) about the instance: its proof is `proof`, an argument of correctness
		args, exInst, hyp = "(inst := "+inst+") ", inst+", ", "("+proof+") "
	}
	return strings.TrimSuffix(src, "end Proof\n") + `
namespace Witness
open Janus.Arm64
def ret : Nat := 0x1000
def s0 : State :=
  { regs := fun i => if i = 0 then (3 : BitVec 64) else if i = 1 then (4 : BitVec 64)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 0x100000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := ⟨fun _ => 0, []⟩ }
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (4 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩
theorem nonvacuous : ∃ (ret : Nat) (s : State) ` + binder + ` (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (` + pre + `) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ (` + post + `)) :=
  ⟨ret, s0, ` + exInst + `3, 4, hret, setup, ` + proof + `, correctness ` + args + `3 4 ` + hyp + `ret hret s0 setup trivial⟩
end Witness
end Proof
`
}
