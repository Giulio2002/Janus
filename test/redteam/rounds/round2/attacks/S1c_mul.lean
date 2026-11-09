import Extracted
/-! S1c: same hole via HMul — statement prints `x * y` but the inline instance computes x + y,
so the proof closes against example.com/basic.Add and the reader sees a multiplication claim. -/
open Janus Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 =
        @HMul.hMul (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
