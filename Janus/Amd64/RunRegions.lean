import Janus.Amd64.Run
import Janus.Amd64.RegionsPres

/-!
# Amd64 runs keep the memory regions

The counterpart of `Janus.RunRegions`: `Amd64.Program.Steps.regions` and `Amd64.Program.run_regions`,
from `Janus.Amd64.step_regions`.
-/

namespace Janus.Amd64

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
    by_cases hx : s.rip.toNat = p.exitAddr
    · rw [run_succ_exit hx] at h; cases h; rfl
    · cases hs : p.stubAt s.rip.toNat with
      | some st => rw [run_succ_stub hx hs] at h; cases h; rfl
      | none =>
        cases hf : p.fetch s.rip.toNat with
        | none => rw [run_succ_noCode hx hs hf] at h; cases h
        | some w =>
          cases hst : Amd64.step w s with
          | error e => rw [run_succ_fault hx hs hf hst] at h; cases h
          | ok s₁ =>
            rw [run_succ_step hx hs hf hst] at h
            rw [ih h, step_regions hst]

end Program

end Janus.Amd64
