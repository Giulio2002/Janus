import Janus
import Extracted

/-! Expected-reason: the lower bound is not exhibited with a returning run (a nil receiver faults at the first instruction; every call meeting the precondition faults). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem atLeast0 : RunsAtLeastOnCall (fun _ => 0) Extracted.program Extracted.entry [0#64]
    (fun s => s.mem.accessible 0 8 false = false) :=
  fun _ _ _ _ _ => rfl

namespace Witness
open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def s0 : State :=
  { regs := fun r_ => if r_ = 0 then 0#64 else if r_ = 4 then BitVec.ofNat 64 wsp else if r_ = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩
set_option maxRecDepth 100000 in
theorem hpre : (fun s : State => s.mem.accessible 0 8 false = false) s0 := by
  dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)
theorem atLeast0 : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    RunsAtLeast 0 (Extracted.program.withExit ret) s :=
  ⟨ret, s0, hret, setup, hpre, rfl⟩
end Witness

end Proof
