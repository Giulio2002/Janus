import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E2d: a beta-redex whose lambda binder is *instance-implicit*, so inside the body the
`*` resolves to the bound instance (an `fvar` with inst-implicit binder info, which
`instArgOk` accepts), and the redex argument is the adding instance. Expected Invalid (the
argument of the redex is in an inst-implicit position of the lambda). -/
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 =
        (fun [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] => x * y) (_i := ⟨fun a b => a + b⟩)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
