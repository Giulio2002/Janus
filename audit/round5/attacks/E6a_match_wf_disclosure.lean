import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E6a (D4 residual): disclosed defs compiled from `match` (a universe-polymorphic
`match_1` auxiliary), well-founded recursion with `termination_by`/`decreasing_by`, and an
explicitly universe-polymorphic def. Records how each is disclosed; expected Verified. -/
namespace Proof
def sel (n : Nat) (a b : BitVec 64) : BitVec 64 :=
  match n with
  | 0 => a + b
  | _ + 1 => a * b
def countdown (n : Nat) (acc : BitVec 64) : BitVec 64 :=
  if h : n = 0 then acc else countdown (n - 1) acc
termination_by n
decreasing_by omega
def poly.{u} {α : Sort u} (_a : α) (x : BitVec 64) : BitVec 64 := x
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = sel 0 x y ∧ countdown 3 (s'.regs 0) = poly True (x + y)) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  all_goals simp [sel, poly, countdown]
end Proof
