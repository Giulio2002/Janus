import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Kernel

namespace Proof

theorem correctness (E : KEnv) :
    EnsuresK Extracted.program E Extracted.entry []
      (fun s _ => GuardOK s 0 ∧ StackOK s 72 0)
      (fun _ k s' k' => k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid) := by
  intro ret hret s k hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩⟩
  apply ReturnsK.of_reaches
  janus_intro hs
  janus_run
  refine ⟨.svc, by rw [siteOf_withExit]; decide, Or.inl ⟨⟨.getpid, ?_, by decide, trivial⟩, ?_⟩⟩
  · simp [svcSys, Sys.ofArm64, setReg]
  rintro s' k' ⟨sc, m', r, hsc, heff, rfl⟩
  simp [svcSys, Sys.ofArm64, setReg] at hsc
  subst hsc
  obtain ⟨rfl, rfl, rfl⟩ := heff
  apply ReturnsK.of_reaches
  janus_run
  exact BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_ofNat])

namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000

def s0 : State :=
  { regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨sp0 - 0x100, 0x200, true⟩, ⟨g0, 0x100, false⟩]⟩ }

def k0 : Kern := {}
def E0 : KEnv := ⟨[], 1024⟩

/-- Fixes the types of the witness's kernel environment and kernel state in the printed statement. -/
def pin (_E : KEnv) (_k : Kern) : Prop := True

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h⟩

theorem pre : GuardOK s0 0 ∧ StackOK s0 72 0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩⟩

/-- The theorem fires: `Getpid()` returns the kernel's pid. -/
theorem returns : ReturnsK (Extracted.program.withExit ret) E0
    (fun s' k' => FFI.ABIReturnC s0 s' ∧ (k' = k0 ∧ s'.regs 0 = BitVec.ofNat 64 k0.pid))
    (fun _ _ => False) s0 k0 :=
  correctness E0 ret hret s0 k0 setup pre

/-- All the hypotheses of `correctness` hold together at a concrete call, and it returns. -/
theorem nonvacuous : ∃ (E : KEnv) (ret : Nat) (s : State) (k : Kern), pin E k ∧ RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧
    (GuardOK s 0 ∧ StackOK s 72 0) ∧
    ReturnsK (Extracted.program.withExit ret) E
      (fun s' k' => FFI.ABIReturnC s s' ∧ (k' = k ∧ s'.regs 0 = BitVec.ofNat 64 k.pid))
      (fun _ _ => False) s k :=
  ⟨E0, ret, s0, k0, trivial, hret, setup, pre, returns⟩

end Witness

end Proof
