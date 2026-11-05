import Janus.Run
import Janus.Arm64.RegionsPres

/-!
# Runs keep the memory regions

Every instruction either leaves `mem` alone or stores through the checked `store`, which only
rewrites bytes (`Janus.Arm64.step_regions`). So a run of any program, however linked
(`Program.link`, `withExit`), keeps `mem.regions`: the set of accessible ranges is fixed for the
whole call, the callee's included. What a callee changes is bytes, never regions.

* `Program.Steps.regions`: `Steps p s k s' → s'.mem.regions = s.mem.regions`.
* `Program.run_regions`: a successful `p.run n s` ends (returned or at a stub) in a state with
  the regions of `s`.
-/

namespace Janus

open Arm64

/-- The state an outcome ends in. -/
def Outcome.state : Outcome → State
  | .returned s => s
  | .stub _ _ s => s

namespace Program

variable {p : Program}

/-- Ordinary steps keep the regions. Holds for every program `p`: also `p.link impl`,
`p.withExit ret`. -/
theorem Steps.regions {s s' : State} {k : Nat} (h : Steps p s k s') :
    s'.mem.regions = s.mem.regions := by
  induction h with
  | refl => rfl
  | step _ _ _ hst _ ih => rw [ih, step_regions hst]

/-- A successful run ends in a state with the regions of its start. -/
theorem run_regions {n : Nat} {s : State} {o : Outcome} (h : p.run n s = .ok o) :
    o.state.mem.regions = s.mem.regions := by
  induction n generalizing s with
  | zero => cases h
  | succ n ih =>
    by_cases hx : s.pc.toNat = p.exitAddr
    · rw [run_succ_exit hx] at h; cases h; rfl
    · cases hs : p.stubAt s.pc.toNat with
      | some st => rw [run_succ_stub hx hs] at h; cases h; rfl
      | none =>
        cases hf : p.fetch s.pc.toNat with
        | none => rw [run_succ_noCode hx hs hf] at h; cases h
        | some w =>
          cases hst : Arm64.step w s with
          | error e => rw [run_succ_fault hx hs hf hst] at h; cases h
          | ok s₁ =>
            rw [run_succ_step hx hs hf hst] at h
            rw [ih h, step_regions hst]

end Program

end Janus
