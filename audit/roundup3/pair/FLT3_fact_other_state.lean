import Extracted

/-! UP3d Faults/fact anchoring row FLT3_fact_other_state.
Expected-reason: does not instantiate any main theorem -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p]
      (fun s => s.mem.accessible (p.toNat + 16) 8 false = true ∧ p.toNat + 16 + 8 ≤ 2 ^ 48)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (p.toNat + 16) 8) := by
  intro ret hret s hs ⟨hacc, hlim⟩
  janus_intro hs
  janus_run

theorem faults :
    ∀ ret, RetAddr Extracted.program ret →
    ∀ s, CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s →
      (∀ r ∈ s.mem.regions, 4096 ≤ r.base) →
      (s.pc.toNat ≠ (Extracted.program.withExit ret).exitAddr ∧
        (Extracted.program.withExit ret).stubAt s.pc.toNat = none ∧
        ∃ w, (Extracted.program.withExit ret).fetch s.pc.toNat = some w ∧
          ∃ a n, Arm64.step w s = .error (.outsideAllocation a n) ∧ a < 4096) ∧
      Faults (Extracted.program.withExit ret) s := by
  intro ret hret s hs hpage
  have h0 : s.regs 0 = 0#64 := hs.args 0 (by decide)
  have hpcn : s.pc.toNat = Extracted.entry := by rw [hs.pc, BitVec.toNat_ofNat]; rfl
  have hfetch : (Extracted.program.withExit ret).fetch s.pc.toNat = some 0xf9400800 := by
    rw [hpcn]; rfl
  have hna : s.mem.accessible 16 8 false = false := by
    unfold Memory.accessible
    simp only [Bool.and_eq_false_iff]
    left
    rw [List.any_eq_false]
    intro r hr
    have := hpage r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1; omega
  have hstep : Arm64.step 0xf9400800 s = .error (.outsideAllocation 16 8) := by
    rw [step_of_decode (i := .ldstUImm 3 1 2 0 0) (by decide)]
    simp only [exec]
    unfold memIndexed baseAddr memSingle load
    simp only [reduceIte, Nat.reduceEqDiff, Bool.false_eq_true, ite_false, h0]
    rw [show ((0#64 : BitVec 64) + BitVec.ofNat 64 (2 * 2 ^ 3)).toNat = 16 from by decide,
      show (2 : Nat) ^ 3 = 8 from rfl, hna]
    rfl
  have hx : s.pc.toNat ≠ (Extracted.program.withExit ret).exitAddr := by
    rw [hpcn, Program.exitAddr_withExit]
    exact hret.ne_of_fetch (pc := Extracted.entry) (w := 0xf9400800) (by rfl)
  have hst : (Extracted.program.withExit ret).stubAt s.pc.toNat = none := by rw [hpcn]; rfl
  refine ⟨⟨hx, hst, 0xf9400800, hfetch, 16, 8, hstep, by decide⟩, ?_⟩
  exact faults_of_steps (Program.Steps.refl s) hx hst hfetch hstep (by simp)


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (0x300000) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0x300000 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p] s ∧ (s.mem.accessible (p.toNat + 16) 8 false = true ∧ p.toNat + 16 + 8 ≤ 2 ^ 48) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = s.mem.readLE (p.toNat + 16) 8)) := by
  refine ⟨ret, s0, (0x300000), hret, setup, ?pre, correctness (0x300000) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide


def sF : State := { s0 with regs := fun i => if i = 0 then 0 else s0.regs i }
theorem setupF : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] sF :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
theorem hregF : ∀ r ∈ sF.mem.regions, 4096 ≤ r.base := by
  simp only [sF, s0, wmem, sp0, g0, hp]; decide
def sG : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 7 then 1 else s0.regs i }
theorem setupG : CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] sG :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩
theorem hregG : ∀ r ∈ sG.mem.regions, 4096 ≤ r.base := by
  simp only [sG, s0, wmem, sp0, g0, hp]; decide

/-- ATTACK: premises and `Faults` at `sG`, but the fact conjunct at the different state `sF`. -/
theorem faults : ∃ (ret : Nat) (s : State) (s2 : State), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [0#64] s2 ∧
    (∀ r ∈ s2.mem.regions, 4096 ≤ r.base) ∧
    (s.pc.toNat ≠ (Extracted.program.withExit ret).exitAddr ∧
        (Extracted.program.withExit ret).stubAt s.pc.toNat = none ∧
        ∃ w, (Extracted.program.withExit ret).fetch s.pc.toNat = some w ∧
          ∃ a n, Arm64.step w s = .error (.outsideAllocation a n) ∧ a < 4096) ∧
    Faults (Extracted.program.withExit ret) s2 :=
  ⟨ret, sF, sG, hret, setupG, hregG, (Proof.faults ret hret sF setupF hregF).1, (Proof.faults ret hret sG setupG hregG).2⟩

end Witness

end Proof
