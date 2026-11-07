import Janus
import Extracted

/-! Red team for the abstract-callee contract: rows 3 and 4 (amd64). Controls: `examples/proofs-amd64/WriteTo/Proof.lean`
verifies. Each theorem below is the same statement with ONE change and the tactic must REFUSE it (`fail_if_success`); the
`sorry` after it is never reached in a passing run and this file is not part of the verified set. Run: `audit/icall/run64.sh`.

* **Row 3, wrong argument bytes:** the contract hypothesis assumes the callee is entered with a slice of length `len + 1`, the
  call passes `len`: `janus64_run` must fail to prove the call-site property `P`.
* **Row 4, forged `fn`:** the itab word is linked to `fn2`, the hypothesis is about `fn`: the executor must refuse the call. -/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts.ICall

theorem wrong_argument_bytes (impl : List Janus.Amd64.Segment) (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len + 1 ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 32 ∧ SPAligned s ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧ Outside ((s.regs 4).toNat - 48) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 3 = e1 ∧ s'.regs 1 = e2) := by
  intro hc ret hret s hs ⟨h8, hfn, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned, CodePtrOK64] at hfn
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF hrt
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 56 rt := hrt.of_sub (by omega) (by omega)
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  fail_if_success (janus64_run [hF] calls [hc])
  sorry

theorem forged_fn (impl : List Janus.Amd64.Segment) (fn fn2 stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧ sc.regs 3 = ptr ∧ sc.regs 1 = len ∧ sc.regs 7 = cap) →
    Ensures (Extracted.program.link impl) Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK64 fn ∧ CodePtrOK64 fn2 ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        StackGuardOK s 0 ∧ StackWritable s (48 + stack) 32 ∧ SPAligned s ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn2 ∧ Outside ((s.regs 4).toNat - 48) 56 rt)
      (fun _ s' => ∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 3 = e1 ∧ s'.regs 1 = e2) := by
  intro hc ret hret s hs ⟨h8, hfn, _, hd, hg, ⟨hle, hnw, hacc⟩, hal, htb, ht, hF, hrt⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned, CodePtrOK64] at hfn
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hacc hle hnw hgl hgb hnw2 hgr hal hd hF hrt
  have hrt' : Outside ((s.regs 4).toNat - 8 - 32 - 8) 56 rt := hrt.of_sub (by omega) (by omega)
  have hal48 : ((s.regs 4).toNat - 48) % 8 = 0 := by omega
  fail_if_success (janus64_run [hF] calls [hc])
  sorry

end Proof
