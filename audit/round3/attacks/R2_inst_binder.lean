import Extracted
/-! R2 (round 3, item 2): a theorem-level instance binder `[inst : HMul ...]` plus a hypothesis
tying it to `+`. The binder's fvar passes `checkInstArgs` (it is an instImplicit binder) and the
statement round-trips (the clean env resolves `*` to the same bound instance). The default
printer renders the abstract instance as `x * y`, so the statement reads as a claim about
multiplication while the Add binary adds. -/
open Janus Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness [inst : HMul (BitVec 64) (BitVec 64) (BitVec 64)]
    (x y : BitVec 64) (h : @HMul.hMul _ _ _ inst x y = x + y) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = @HMul.hMul _ _ _ inst x y) := by
  intro ret hret s hs _
  rw [h]
  janus_intro hs
  janus_run
end Proof
