import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5f: E5e with the instance parameter hidden behind a type alias
(`Pred := HMul … → Prop`, a *default* binder, which a local still treats as an instance because
of its class type) so the def's type shows no `[…]` binder. Expected Invalid after the fix. -/
namespace Proof
def Pred : Type := HMul (BitVec 64) (BitVec 64) (BitVec 64) → Prop
def isProd (x y r : BitVec 64) : Pred := fun (_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)) => r = x * y
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => @Exists (HMul (BitVec 64) (BitVec 64) (BitVec 64)) (isProd x y (s'.regs 0))) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
end Proof
