import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E3b: a proof-local structure *extending* `Janus.Arm64.State`, whose `regs` field
(inherited) is overridden by a lift that changes X0. Expected Invalid. -/
namespace Proof
structure MyState extends State where
  extra : Nat
def lift (x y : BitVec 64) (s : State) : MyState :=
  { s with regs := fun r => if r = 0 then x * y else s.regs r, extra := 0 }
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (lift x y s').regs 0 = x * y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals first | rfl | simp [lift]
end Proof
