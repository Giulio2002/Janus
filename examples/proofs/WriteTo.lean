import Extracted

/-!
# `WriteTo(w io.Writer, b []byte) (int, error)` calls `w.Write(b)` on an arbitrary writer

**Guarantee.** For **every** code address `fn`, every memory `rt` the callee may write, every relation `R` of
its results to its arguments, and every call state of `example.com/basic.WriteTo` in which the
stack-growth prologue falls through, `SP` is aligned with the callee's stack and the function's frame writable,
the itab word `tab` of the writer has `Fun[0] = fn` (`s.mem.readLE (tab + 24) 8 = fn`, 8 readable bytes) and `rt` is
apart from the function's frame:

* if the code at `fn` satisfies `ICallContract` (the Go ABI only: a return to the caller with `SP`, `X18`, `X28`,
  `X29` preserved, memory changed only in `rt` and the callee's stack, the slice bytes unchanged, results related by
  `R` to the arguments), then `WriteTo` returns, and
* the call to `fn` is **entered with the receiver `w` and the slice `(ptr, len, cap)` that `WriteTo` received** (the
  call-site property `P` is what `janus_run` proves at the call: the theorem assumes the callee only for such calls),
* the results of `WriteTo` are the callee's results, unchanged: `R w ptr len cap n e₁ e₂` and
  `(X0, X1, X2) = (n, e₁, e₂)`,
* the bytes of the slice are unchanged.

**What it assumes.** Only `ICallContract fn …` (a hypothesis about code that is not extracted: the printed statement
shows it) and the link between the itab word and `fn`. Nothing is assumed about which writer it is, nor that it leaves
the heap alone.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.ICall

namespace Proof

theorem correctness (fn stack : Nat) (rt : List (Nat × Nat)) (R : Res) (tab w ptr len cap : BitVec 64) :
    ICallContract Extracted.program fn stack 48 rt R
      (fun sc => sc.regs 0 = w ∧ sc.regs 1 = ptr ∧ sc.regs 2 = len ∧ sc.regs 3 = cap) →
    Ensures Extracted.program Extracted.entry [tab, w, ptr, len, cap]
      (fun s => 8 ≤ stack ∧ fn % 4 = 0 ∧ fn < 2 ^ 56 ∧ Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 56) 88 ∧
        Disjoint ptr.toNat len.toNat (s.sp.toNat - 56) 88 ∧ GuardOK s 0 ∧ StackOK s (48 + stack) 40 ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        Outside (s.sp.toNat - 56) 56 rt)
      (fun s s' => (∃ n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = n ∧ s'.regs 1 = e1 ∧ s'.regs 2 = e2) ∧
        ∀ x, ptr.toNat ≤ x → x < ptr.toNat + len.toNat → s'.mem.readLE x 1 = s.mem.readLE x 1) := by
  intro hc ret hret s hs ⟨h8, hfn4, hfn, hd, hdp, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, htb, ht, hF, hrt⟩
  janus_intro hs
  simp only [Disjoint] at hd hdp
  have hrt' : Outside (s.sp.toNat - 48 - 8) (48 + 8) rt := hrt.of_sub (by omega) (by omega)
  janus_run [hF] calls [hc]
  case hq =>
    rename_i _ hby hR
    refine ⟨⟨_, _, _, hR, rfl, rfl, rfl⟩, fun x h1 h2 => ?_⟩
    rw [hby x h1 h2]
    rw [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_of_disjoint,
      Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_of_disjoint] <;> omega

end Proof
