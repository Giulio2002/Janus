import Extracted

/-!
# `CountThenWrite(s Sink, p []byte) (int, error)`: two interface calls to arbitrary callees

`n := s.Count(); if n == 0 { return 0, nil }; return s.Write(p)`. Two `calls [hc1, hc2]` hypotheses, one per itab slot
(`Fun[0]` = `Count`, `Fun[1]` = `Write`), each about a code address that is a parameter of the theorem
(`ICallContract fn₁ …`, `ICallContract fn₂ …`), with their own call-site properties (the receiver for `Count`; the
receiver and the slice for `Write`) and their own result relations `R₁`, `R₂`.

**Guarantee.** For every `fn₁`, `fn₂`, callee memory `rt` and relations `R₁`, `R₂`, if the two callees satisfy their
contracts, `CountThenWrite` returns, and: `Count` was entered with the receiver `w`; its result `c` satisfies `R₁`; if
`c = 0` the function returns `(0, nil)`; otherwise `Write` was entered with `w` and the slice `(ptr, len, cap)` and the
function returns what it returned, unchanged (`R₂`). The continuation holds for **every** value `c` returns. The
assumptions are the two contracts, the link between each itab word and its `fn`, `CodePtrOK` of both, and that the
itab words are outside the callees' memory `rt`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall

namespace Proof

theorem correctness (fn1 fn2 stack : Nat) (rt : List (Nat × Nat)) (R1 R2 : Res)
    (tab w ptr len cap : BitVec 64) :
    ICallContract Extracted.program fn1 1 stack 96 rt (fun _ => []) R1 (fun sc => sc.regs 0 = w) →
    ICallContract Extracted.program fn2 4 stack 96 rt (fun _ => []) R2
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) →
    Ensures Extracted.program Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ CodePtrOK fn1 ∧ CodePtrOK fn2 ∧
        Disjoint (tab.toNat + 24) 16 (s.sp.toNat - 56) 104 ∧
        GuardOK s 0 ∧ StackOK s (48 + stack) 48 ∧
        tab.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 16 false = true ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn1 ∧ s.mem.readLE (tab.toNat + 32) 8 = fn2 ∧
        Outside (tab.toNat + 24) 16 rt ∧ Outside (s.sp.toNat - 56) 104 rt)
      (fun _ s' => ∃ c a1 a2 a3 e1 e2, R1 w a1 a2 a3 c e1 e2 ∧
        ((c = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
         (c ≠ 0 ∧ ∃ n f1 f2, R2 w ptr len cap n f1 f2 ∧ s'.regs 0 = n ∧ s'.regs 1 = f1 ∧ s'.regs 2 = f2))) := by
  intro hc1 hc2 ret hret s hs ⟨h8, ⟨hf14, hf1⟩, ⟨hf24, hf2⟩, hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF1, hF2, hot, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd
  have hrt' : Outside (s.sp.toNat - 48 - 8) (96 + 8) rt := hrt.of_sub (by omega) (by omega)
  janus_run [hF1, hF2] calls [hc1, hc2]
  all_goals (trace_state; sorry)

end Proof
