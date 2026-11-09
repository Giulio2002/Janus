import Extracted

/-!
# Red team for the abstract-callee contract: rows 3 and 4 (arm64)

Controls: `examples/proofs/WriteTo.lean` verifies. Each theorem below is the same statement with ONE change, and the
tactic must REFUSE it (`fail_if_success`); the `sorry` after it is never reached in a passing run, and this file is
not part of the verified set. Run: `audit/icall/run.sh` (it fails if a variant is accepted).

* **Row 3, wrong argument bytes:** the contract hypothesis assumes the callee is entered with a slice of length
  `len + 1`, the call passes `len`. `janus_run` must fail to prove the call-site property `P` (the precondition of the
  callee's summary).
* **Row 4, forged `fn`:** the itab word is linked to `fn2`, the hypothesis is about `fn`: the call target is not the
  hypothesis' entry, so the executor must refuse the call (the pc is not a concrete address).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall

namespace Proof

namespace Proof

theorem wrong_argument_bytes (impl : List Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract (Extracted.program.link impl) fn 4 stack 48 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len + 1 ∧ sc.regs 3 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK fn ∧ Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 56) 88 ∧
        GuardOK s 0 ∧ StackOK s (48 + stack) 40 ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        Outside (s.sp.toNat - 56) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 1 = e1 ∧ s'.regs 2 = e2) := by
  intro hc ret hret s hs ⟨h8, ⟨hfn4, hfn⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hrt' : Outside (s.sp.toNat - 48 - 8) (48 + 8) rt := hrt.of_sub (by omega) (by omega)
  fail_if_success (janus_run [hF] calls [hc])
  sorry

theorem forged_fn (impl : List Segment) (fn fn2 stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract (Extracted.program.link impl) fn 4 stack 48 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK fn ∧ CodePtrOK fn2 ∧ Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 56) 88 ∧
        GuardOK s 0 ∧ StackOK s (48 + stack) 40 ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ s.mem.readLE (tab.toNat + 24) 8 = fn2 ∧
        Outside (s.sp.toNat - 56) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 1 = e1 ∧ s'.regs 2 = e2) := by
  intro hc ret hret s hs ⟨h8, ⟨hfn4, hfn⟩, _, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hrt' : Outside (s.sp.toNat - 48 - 8) (48 + 8) rt := hrt.of_sub (by omega) (by omega)
  fail_if_success (janus_run [hF] calls [hc])
  sorry

end Proof
