import Janus
import Extracted

/-! Expected-reason: Lean rejected the proof (the bound is too small). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem within (x y : BitVec 64) :
    EnsuresWithin (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun s => StackWritable s 0 8) (fun _ s' => results 1 s' = [if y.toNat < x.toNat then x else y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  all_goals simp [hbr]

end Proof
