import JanusASL.Proofs.FpSame.ExecA
import JanusASL.Proofs.FpSame.ExecB
import JanusASL.Proofs.FpSame.ExecC

namespace JanusASL.FpS
open Janus.Arm64

local macro "fp_same2" : tactic => `(tactic| (
  dsimp only [FpSame]
  repeat' (first | split | skip)
  all_goals simp only [writeZR_vregs, writeZR_fpcr, writeZR_fpsr, writeSP_vregs, writeSP_fpcr, writeSP_fpsr,
    setX_vregs, setX_fpcr, setX_fpsr, setXSP_vregs, setXSP_fpcr, setXSP_fpsr, setFlags_vregs, setFlags_fpcr,
    setFlags_fpsr, next_vregs, next_fpcr, next_fpsr, and_self, execAddSubImm_vregs, execAddSubImm_fpcr, execAddSubImm_fpsr, execAddSubShifted_vregs, execAddSubShifted_fpcr, execAddSubShifted_fpsr, execAddSubExt_vregs, execAddSubExt_fpcr, execAddSubExt_fpsr, execAddSubCarry_vregs, execAddSubCarry_fpcr, execAddSubCarry_fpsr, execLogicalImm_vregs, execLogicalImm_fpcr, execLogicalImm_fpsr, execLogicalShifted_vregs, execLogicalShifted_fpcr, execLogicalShifted_fpsr, execMoveWide_vregs, execMoveWide_fpcr, execMoveWide_fpsr, execBitfield_vregs, execBitfield_fpcr, execBitfield_fpsr, execExtr_vregs, execExtr_fpcr, execExtr_fpsr, execCondSel_vregs, execCondSel_fpcr, execCondSel_fpsr, execCondCmp_vregs, execCondCmp_fpcr, execCondCmp_fpsr, execMadd_vregs, execMadd_fpcr, execMadd_fpsr, execMaddl_vregs, execMaddl_fpcr, execMaddl_fpsr, execMulh_vregs, execMulh_fpcr, execMulh_fpsr, execDiv_vregs, execDiv_fpcr, execDiv_fpsr, execShiftV_vregs, execShiftV_fpcr, execShiftV_fpsr, execRbit_vregs, execRbit_fpcr, execRbit_fpsr, execRev_vregs, execRev_fpcr, execRev_fpsr, execClz_vregs, execClz_fpcr, execClz_fpsr, execCls_vregs, execCls_fpcr, execCls_fpsr]))

theorem fp_exec_addSubExt (sf op S : Bool) (rm : Nat) (option : ExtendType) (imm3 rn rd : Nat) (js js' : State)
    (h : exec (.addSubExt sf op S rm option imm3 rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_addSubCarry (sf op S : Bool) (rm rn rd : Nat) (js js' : State)
    (h : exec (.addSubCarry sf op S rm rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_condCmpReg (sf op : Bool) (rm cond rn nzcv : Nat) (js js' : State)
    (h : exec (.condCmpReg sf op rm cond rn nzcv) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_condCmpImm (sf op : Bool) (imm5 cond rn nzcv : Nat) (js js' : State)
    (h : exec (.condCmpImm sf op imm5 cond rn nzcv) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_condSel (sf op : Bool) (rm cond : Nat) (o2 : Bool) (rn rd : Nat) (js js' : State)
    (h : exec (.condSel sf op rm cond o2 rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_madd (sf o0 : Bool) (rm ra rn rd : Nat) (js js' : State)
    (h : exec (.madd sf o0 rm ra rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_maddl (U o0 : Bool) (rm ra rn rd : Nat) (js js' : State)
    (h : exec (.maddl U o0 rm ra rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

theorem fp_exec_mulh (U : Bool) (rm rn rd : Nat) (js js' : State)
    (h : exec (.mulh U rm rn rd) js = .ok js') : FpSame js js' := by
  simp only [exec] at h
  cases h
  fp_same2

end JanusASL.FpS
