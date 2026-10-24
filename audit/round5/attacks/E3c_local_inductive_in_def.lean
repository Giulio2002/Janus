import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E3c: a proof-local inductive used only inside a disclosed def body (the statement
names only the def). Expected Invalid (`collectLocalDefs` follows the body's constants). -/
namespace Proof
inductive Op | add | mul
def run : Op → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .mul, a, b => a * b
def mulOp (a b : BitVec 64) : BitVec 64 := run .add a b
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = mulOp x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  rfl
end Proof
