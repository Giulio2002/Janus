import Janus.Arm64.Exec

/-! # The floating-point state integer steps leave alone (Janus side)

Every integer `exec` builds its result from the pre-state by `setX`, `writeZR`, `setFlags`, `next` and
record updates of `pc`, none of which touches `vregs`, `fpcr` or `fpsr`. -/

namespace JanusASL.FpS
open Janus.Arm64

/-- The floating-point state (`V`, `FPCR`, `FPSR`) that a step leaves alone. -/
def FpSame (s t : State) : Prop := t.vregs = s.vregs ∧ t.fpcr = s.fpcr ∧ t.fpsr = s.fpsr

theorem writeZR_fp (s : State) (r : Nat) (v : W64) :
    (s.writeZR r v).vregs = s.vregs ∧ (s.writeZR r v).fpcr = s.fpcr ∧ (s.writeZR r v).fpsr = s.fpsr := by
  unfold State.writeZR; split <;> exact ⟨rfl, rfl, rfl⟩
theorem writeSP_fp (s : State) (r : Nat) (v : W64) :
    (s.writeSP r v).vregs = s.vregs ∧ (s.writeSP r v).fpcr = s.fpcr ∧ (s.writeSP r v).fpsr = s.fpsr := by
  unfold State.writeSP; split <;> exact ⟨rfl, rfl, rfl⟩

@[simp] theorem writeZR_vregs (s : State) (r : Nat) (v : W64) : (s.writeZR r v).vregs = s.vregs := (writeZR_fp s r v).1
@[simp] theorem writeZR_fpcr (s : State) (r : Nat) (v : W64) : (s.writeZR r v).fpcr = s.fpcr := (writeZR_fp s r v).2.1
@[simp] theorem writeZR_fpsr (s : State) (r : Nat) (v : W64) : (s.writeZR r v).fpsr = s.fpsr := (writeZR_fp s r v).2.2
@[simp] theorem writeSP_vregs (s : State) (r : Nat) (v : W64) : (s.writeSP r v).vregs = s.vregs := (writeSP_fp s r v).1
@[simp] theorem writeSP_fpcr (s : State) (r : Nat) (v : W64) : (s.writeSP r v).fpcr = s.fpcr := (writeSP_fp s r v).2.1
@[simp] theorem writeSP_fpsr (s : State) (r : Nat) (v : W64) : (s.writeSP r v).fpsr = s.fpsr := (writeSP_fp s r v).2.2
@[simp] theorem setX_vregs {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setX r v).vregs = s.vregs := writeZR_vregs ..
@[simp] theorem setX_fpcr {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setX r v).fpcr = s.fpcr := writeZR_fpcr ..
@[simp] theorem setX_fpsr {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setX r v).fpsr = s.fpsr := writeZR_fpsr ..
@[simp] theorem setXSP_vregs {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setXSP r v).vregs = s.vregs := writeSP_vregs ..
@[simp] theorem setXSP_fpcr {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setXSP r v).fpcr = s.fpcr := writeSP_fpcr ..
@[simp] theorem setXSP_fpsr {N : Nat} (s : State) (r : Nat) (v : BitVec N) : (s.setXSP r v).fpsr = s.fpsr := writeSP_fpsr ..
@[simp] theorem setFlags_vregs (s : State) (f : Flags) : (s.setFlags f).vregs = s.vregs := rfl
@[simp] theorem setFlags_fpcr (s : State) (f : Flags) : (s.setFlags f).fpcr = s.fpcr := rfl
@[simp] theorem setFlags_fpsr (s : State) (f : Flags) : (s.setFlags f).fpsr = s.fpsr := rfl
@[simp] theorem next_vregs (s : State) : s.next.vregs = s.vregs := rfl
@[simp] theorem next_fpcr (s : State) : s.next.fpcr = s.fpcr := rfl
@[simp] theorem next_fpsr (s : State) : s.next.fpsr = s.fpsr := rfl

macro "fp_same" : tactic => `(tactic| (
  dsimp only [FpSame]
  repeat' (first | split | skip)
  all_goals simp only [writeZR_vregs, writeZR_fpcr, writeZR_fpsr, writeSP_vregs, writeSP_fpcr, writeSP_fpsr,
    setX_vregs, setX_fpcr, setX_fpsr, setXSP_vregs, setXSP_fpcr, setXSP_fpsr, setFlags_vregs, setFlags_fpcr,
    setFlags_fpsr, next_vregs, next_fpcr, next_fpsr, and_self]))


end JanusASL.FpS
