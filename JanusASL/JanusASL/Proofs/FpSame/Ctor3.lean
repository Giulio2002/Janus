import JanusASL.Proofs.FpSame.ExecA
import JanusASL.Proofs.FpSame.ExecB
import JanusASL.Proofs.FpSame.ExecC

namespace JanusASL.FpS
open Janus.Arm64

macro "fp_same2" : tactic => `(tactic| (
  dsimp only [FpSame]
  repeat' (first | split | skip)
  all_goals simp only [writeZR_vregs, writeZR_fpcr, writeZR_fpsr, writeSP_vregs, writeSP_fpcr, writeSP_fpsr,
    setX_vregs, setX_fpcr, setX_fpsr, setXSP_vregs, setXSP_fpcr, setXSP_fpsr, setFlags_vregs, setFlags_fpcr,
    setFlags_fpsr, next_vregs, next_fpcr, next_fpsr, and_self, execAddSubImm_vregs, execAddSubImm_fpcr, execAddSubImm_fpsr, execAddSubShifted_vregs, execAddSubShifted_fpcr, execAddSubShifted_fpsr, execAddSubExt_vregs, execAddSubExt_fpcr, execAddSubExt_fpsr, execAddSubCarry_vregs, execAddSubCarry_fpcr, execAddSubCarry_fpsr, execLogicalImm_vregs, execLogicalImm_fpcr, execLogicalImm_fpsr, execLogicalShifted_vregs, execLogicalShifted_fpcr, execLogicalShifted_fpsr, execMoveWide_vregs, execMoveWide_fpcr, execMoveWide_fpsr, execBitfield_vregs, execBitfield_fpcr, execBitfield_fpsr, execExtr_vregs, execExtr_fpcr, execExtr_fpsr, execCondSel_vregs, execCondSel_fpcr, execCondSel_fpsr, execCondCmp_vregs, execCondCmp_fpcr, execCondCmp_fpsr, execMadd_vregs, execMadd_fpcr, execMadd_fpsr, execMaddl_vregs, execMaddl_fpcr, execMaddl_fpsr, execMulh_vregs, execMulh_fpcr, execMulh_fpsr, execDiv_vregs, execDiv_fpcr, execDiv_fpsr, execShiftV_vregs, execShiftV_fpcr, execShiftV_fpsr, execRbit_vregs, execRbit_fpcr, execRbit_fpsr, execRev_vregs, execRev_fpcr, execRev_fpsr, execClz_vregs, execClz_fpcr, execClz_fpsr, execCls_vregs, execCls_fpcr, execCls_fpsr]))

theorem fp_exec_div (sf o1 : Bool) (rm rn rd : Nat) (js js' : State)
    (h : exec (.div sf o1 rm rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_shiftV (sf : Bool) (t : ShiftType) (rm rn rd : Nat) (js js' : State)
    (h : exec (.shiftV sf t rm rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_rbit (sf : Bool) (rn rd : Nat) (js js' : State)
    (h : exec (.rbit sf rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_rev (sf : Bool) (opc rn rd : Nat) (js js' : State)
    (h : exec (.rev sf opc rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_clz (sf : Bool) (rn rd : Nat) (js js' : State)
    (h : exec (.clz sf rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_cls (sf : Bool) (rn rd : Nat) (js js' : State)
    (h : exec (.cls sf rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

end JanusASL.FpS
