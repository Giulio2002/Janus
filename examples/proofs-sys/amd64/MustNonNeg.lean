import Janus
import Extracted

/-!
# `MustNonNeg(x int64) int64`: returns `x`, or ends in a breakpoint trap (amd64)

The amd64 build of `examples/sys.MustNonNeg` (see the arm64 proof): `runtime.breakpoint` is
`INT3`, which gets a `.trap` stub; executed, it faults with `Fault.trap pc 5` (`SIGTRAP`).

* `correctness`: for `0 ≤ x` (signed) the call returns `x` in `RAX`;
* `traps`: for `x < 0` the run ends in the breakpoint trap.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Kernel Janus.Amd64.Kernel

namespace Proof

theorem msb_of_nonneg (x : BitVec 64) (hx : 0 ≤ x.toInt) : x.msb = false := by
  have h : x.toNat < 2 ^ 63 := by
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
    · exact h
    · exact absurd ((BitVec.toInt_neg_iff (x := x)).mpr (by omega)) (by omega)
  rw [BitVec.msb_eq_decide]; simp; omega

theorem msb_of_neg (x : BitVec 64) (hx : x.toInt < 0) : x.msb = true := by
  have h : 2 ^ 63 ≤ x.toNat := by have := (BitVec.toInt_neg_iff (x := x)).mp hx; omega
  rw [BitVec.msb_eq_decide]; simp; omega

theorem correctness (x : BitVec 64) (hx : 0 ≤ x.toInt) :
    Ensures Extracted.program Extracted.entry [x] (fun s => StackGuardOK s 0 ∧ StackWritable s 16 16)
      (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩⟩
  have hm := msb_of_nonneg x hx
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw
  janus64_run [hm]

theorem traps (x : BitVec 64) (hx : x.toInt < 0) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s)
    (hg : StackGuardOK s 0) (hst : StackWritable s 16 16) :
    Janus.Amd64.Kernel.Traps (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hb, ha, hw⟩ := hst
  have hm := msb_of_neg x hx
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw
  unfold Janus.Amd64.Kernel.Traps
  janus64_run [hm]
  rw [Janus.Amd64.Kernel.trapAt_withExit]
  decide

namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000

def bytes (a : Nat) : Byte := if a = sp0 + 2 then 0x20 else 0

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then 5 else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(5 : BitVec 64)] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 16 16 :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns `x`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : Amd64.State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ 0 ≤ x.toInt ∧
    (StackGuardOK s 0 ∧ StackWritable s 16 16) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = x) :=
  ⟨ret, s0, 5, hret, setup, by decide, hpre, correctness 5 (by decide) ret hret s0 setup hpre⟩

def sT : Amd64.State :=
  { regs := fun i => if i = 0 then 0xFFFFFFFFFFFFFFFF else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩]⟩ }


theorem setupT : CallSetup (Extracted.program.withExit ret) Extracted.entry [(0xFFFFFFFFFFFFFFFF : BitVec 64)] sT :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpreT : StackGuardOK sT 0 ∧ StackWritable sT 16 16 :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩⟩


/-- All the hypotheses of `traps` hold together at a concrete call with a negative `x`, and the call traps. -/
theorem traps : ∃ (ret : Nat) (s : Amd64.State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ x.toInt < 0 ∧
    (StackGuardOK s 0 ∧ StackWritable s 16 16) ∧
    Janus.Amd64.Kernel.Traps (Extracted.program.withExit ret) s :=
  ⟨ret, sT, 0xFFFFFFFFFFFFFFFF, hret, setupT, by decide, hpreT, Proof.traps 0xFFFFFFFFFFFFFFFF (by decide) ret hret sT setupT hpreT.1 hpreT.2⟩

end Witness

end Proof
