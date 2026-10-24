import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5a: an existential whose binder is *instance-implicit*, inside a disclosed def.
Inside the body `x * y` resolves to the bound instance, so `∃ [i : HMul …], r = x * y` is
trivially true for every `r` (take `hMul := fun _ _ => r`). `checkInstArgs` accepts the
bound variable (an inst-implicit binder), and the disclosure does not round-trip (read back,
`*` is the canonical multiplication), so it is shown tagged `[not round-tripped]`. -/
namespace Proof
def isProd (x y r : BitVec 64) : Prop :=
  Exists fun [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] => r = x * y
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => isProd x y (s'.regs 0)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
end Proof
