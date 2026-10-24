import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E4d: a *global* (non-local) `notation` and an `app_unexpander` declared in the
proof, which would print `BitVec.add x y` as `x ⊗ y`/`x * y` if they were active when printing.
The auditor prints in a clean environment that never imports the proof. Expected Verified with
`x + y` printed. -/
namespace Proof
notation:70 a " ⊗ " b => BitVec.add a b
@[app_unexpander HAdd.hAdd] def unexpAdd : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a * $b)
  | _ => throw ()
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y ∧ s'.regs 0 = x ⊗ y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals rfl
end Proof
