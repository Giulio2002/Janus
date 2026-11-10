import Extracted

/-! Expected-reason: the lower bound is not exhibited with a returning run. RunsAtLeast (here 0, and it would hold for every
bound up to the faulting instruction) is true of a state whose call faults; no call meeting this precondition returns. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem atLeast0 : RunsAtLeastOnCall (fun _ => 0) Extracted.program Extracted.entry [0#64]
    (fun s => s.mem.accessible 0 8 false = false) :=
  fun _ _ _ _ _ => rfl

namespace Witness
def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000
def wbytes (a : Nat) : Byte := 0
def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩
def s0 : State :=
  { regs := fun i => if i = 0 then (0) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atLeast0 : ∃ (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s ∧ (s.mem.accessible 0 8 false = false) ∧
    RunsAtLeast 0 (Extracted.program.withExit ret) s := by
  refine ⟨ret, s0, hret, setup, ?pre, rfl⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Disjoint, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide
end Witness

end Proof
