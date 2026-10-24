import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 7 K1a: the most misleading *true* statement found built only from standard Lean
operations. On `example.com/basic.Add` it reads "Add returns `x` and returns `y`, and its result
is 0": `x.toNat - r.toNat = 0` (truncating Nat subtraction: only `x ≤ r`), `r * 2 ^ 64 = 0`
(wrapping `^` at `BitVec 64`: `2 ^ 64 = 0`), and `r.toNat / 0 = 0` (total division). It is true
of every input, round-trips, and verifies. Round 7 adds notes for each operation. -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 * 2 ^ 64 = 0 ∧ (s'.regs 0).toNat / 0 = 0 ∧
        (x.toNat + y.toNat) % 2 ^ 64 - (s'.regs 0).toNat = 0) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  have h : (2#64 ^ 64 : BitVec 64) = 0 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩ <;> simp [h]
end Proof
