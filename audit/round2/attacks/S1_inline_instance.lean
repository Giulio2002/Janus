import Extracted
/-! S1: a fake instance built inline from a trusted core constructor (HSub.mk). No proof-local
constant appears in the statement, so the A1 instance rule and the class-valued-def rule never
fire, and the clean-environment printer shows `x - y` for what is really `x + y`. Target:
example.com/basic.Add, which computes x + y. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic
namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 =
        @HSub.hSub (BitVec 64) (BitVec 64) (BitVec 64) ⟨fun a b => a + b⟩ x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
