import Janus
import Extracted

/-! Expected-reason: the instruction bound mentions the execution of the program. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem real (x y : BitVec 64) :
    EnsuresWithin (fun _ => 4) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

def lenOf (s : State) : Nat :=
  match Extracted.program.run 8 s with
  | .ok (.returned s') => (s'.regs 0).toNat
  | _ => 0

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun s => lenOf s + 4) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) :=
  (real x y).mono_bound fun _ _ => Nat.le_add_left _ _

end Proof
