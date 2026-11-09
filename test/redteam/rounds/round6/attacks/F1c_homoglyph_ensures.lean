import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 6 F1c: `Janus.GoABI.Εnsures` (GREEK CAPITAL EPSILON), a proof-local def that is `True`.
The statement prints exactly like a real `Janus.GoABI.Ensures` claim that `Add` returns `x * y`.
The name has no `Extracted` component, so only the round-6 plain-name rule rejects it.
Expected Invalid (lookalike letters). -/
def Janus.GoABI.Εnsures (_p : Program) (_entry : Nat) (_args : List (BitVec 64))
    (_pre : State → Prop) (_post : State → State → Prop) : Prop := True
namespace Proof
theorem correctness (x y : BitVec 64) :
    Janus.GoABI.Εnsures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x * y) := trivial
end Proof
