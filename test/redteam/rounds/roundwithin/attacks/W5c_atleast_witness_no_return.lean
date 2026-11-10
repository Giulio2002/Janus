import Extracted

/-! Expected-reason: the lower bound is not exhibited with a returning run. Witness.atLeast states RunsAtLeast but no Returns from the same state. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem atLeast (x y : BitVec 64) :
    RunsAtLeastOnCall (fun _ => 3) Extracted.program Extracted.entry [x, y] (fun _ => True) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run

namespace Witness

def ret : Nat := 0x1000
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000
def wbytes (a : Nat) : Byte := 0
def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩
def s0 : State :=
  { regs := fun i => if i = 0 then (3) else if i = 1 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(3 : BitVec 64), (5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem atLeast : ∃ (ret : Nat) (s : State) (x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (True) ∧
    RunsAtLeast 3 (Extracted.program.withExit ret) s :=
  ⟨ret, s0, (3), (5), hret, setup, trivial, Proof.atLeast (3) (5) ret hret s0 setup trivial⟩
end Witness

end Proof
