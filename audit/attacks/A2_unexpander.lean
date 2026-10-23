import Extracted
/-! ATTACK A2: an `app_unexpander` makes `Shown P Q` (which means `Q`) print as `P`. The checked
statement is `Ensures ... True`-like; the printed statement claims Add returns x*y. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

def Shown (_shown : Prop) (actual : Prop) : Prop := actual

@[app_unexpander Shown] def unexpShown : Lean.PrettyPrinter.Unexpander
  | `($_ $p $_) => `($p)
  | _ => throw ()

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => Shown ((s'.regs 0).toNat = x.toNat * y.toNat) True) := by
  intro ret hret s hs hp
  obtain ⟨f, s', h1, h2, _⟩ := honest x y ret hret s hs hp
  exact ⟨f, s', h1, h2, trivial⟩
end Proof
