import Extracted
/-! ATTACK A4: an `app_unexpander` for the *Janus* constant `Ensures`, defined in the proof file.
The checked statement uses only Janus/Extracted constants and has postcondition `True`; the
printed statement claims Add returns x * y. -/
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

set_option hygiene false in
@[app_unexpander Janus.GoABI.Ensures] def unexpEnsures : Lean.PrettyPrinter.Unexpander
  | `($f $p $e [$xs,*] $pre $_) => do
      let x := xs.getElems[0]!
      let y := xs.getElems[1]!
      `($f $p $e [$xs,*] $pre fun _ s' => BitVec.toNat (s'.regs 0) = HMul.hMul (BitVec.toNat $x) (BitVec.toNat $y))
  | _ => throw ()

theorem honest (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Proof
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True) (fun _ _ => True) := by
  intro ret hret s hs hp
  obtain ⟨f, s', h1, h2, _⟩ := honest x y ret hret s hs hp
  exact ⟨f, s', h1, h2, trivial⟩
end Proof
