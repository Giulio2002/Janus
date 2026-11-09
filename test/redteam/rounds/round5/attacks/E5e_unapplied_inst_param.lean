import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E5e: the E5 vacuity without any binder in the statement. A proof-local def takes its
`HMul` instance as its *last* parameter (`[_i : HMul …]`, a top-level parameter, so its body
passes the E5 binder rule), and the statement passes the def to `Exists` *unapplied* to that
parameter: `Exists (Proof.isProd x y (s'.regs 0))`, i.e. "there is a multiplication with
`regs 0 = x * y`", true for every result. Expected Invalid after the fix. -/
namespace Proof
def isProd (x y r : BitVec 64) [_i : HMul (BitVec 64) (BitVec 64) (BitVec 64)] : Prop := r = x * y
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => @Exists (HMul (BitVec 64) (BitVec 64) (BitVec 64)) (@isProd x y (s'.regs 0))) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  exact ⟨⟨fun _ _ => x + y⟩, rfl⟩
end Proof
