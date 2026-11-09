import JanusASL.Proofs.FP.Compare
import JanusASL.Proofs.FP.ImpDef

/-! # The floating-point part of the state relation

`FPRel js s`: the Sail state holds Janus' `V0`–`V31` (the low 128 bits of `_Z[i]`), and FPCR
and FPSR (zero-extended); Janus' FPCR has its RES0 bits (3–7, 14, 27–31) clear, so the ASL's
`FPCR_read` (which masks them) returns it unchanged. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The FPCR bits `FPCR_read` keeps (the others are RES0 or masked by the configuration). -/
def fpcrKeep : Nat := 0x7FFBF07

structure FPRel (js : Janus.Arm64.State) (s : SState) : Prop where
  z : ∃ z : Vector (BitVec 2048) 32, s.regs.get? ._Z = some z ∧ ∀ i < 32, (z[i]!).toNat % 2 ^ 128 = (js.vregs i).toNat
  fpcr : s.regs.get? .FPCR = some (js.fpcr.setWidth 64)
  fpcrRes0 : js.fpcr.toNat &&& fpcrKeep = js.fpcr.toNat
  fpsr : s.regs.get? .FPSR = some (js.fpsr.setWidth 64)

/-- The registers `FPRel` reads. -/
def fpRelRegs : List Register := [._Z, .FPCR, .FPSR]

theorem FPRel.of_eq {js : Janus.Arm64.State} {s s' : SState} (h : FPRel js s)
    (e : ∀ r ∈ fpRelRegs, s'.regs.get? r = s.regs.get? r) : FPRel js s' := by
  obtain ⟨z, hz, hzv⟩ := h.z
  exact { z := ⟨z, by rw [e _ (by decide)]; exact hz, hzv⟩
          fpcr := by rw [e _ (by decide)]; exact h.fpcr
          fpcrRes0 := h.fpcrRes0
          fpsr := by rw [e _ (by decide)]; exact h.fpsr }

theorem vget_int (z : Vector (BitVec 2048) 32) (n : Nat) : z[(n : Int)]! = z[n]! := by
  simp [getElem!_def, GetElem?.getElem?]

theorem run_V_read {js : Janus.Arm64.State} {s : SState} (h : FPRel js s) {n : Nat} (hn : n < 32) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 ∨ w = 128) :
    (V_read (n : Int) w).run s = .ok (BitVec.ofNat w (js.getV n w)) s := by
  obtain ⟨z, hz, hzv⟩ := h.z
  have hw' : (w == 8 || (w == 16 || (w == 32 || (w == 64 || w == 128)))) = true := by
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
  cfg_simp [V_read, run_readReg hz, hw', show (0 : Int) ≤ n from Int.natCast_nonneg n, show (n : Int) ≤ 31 by omega]
  rw [vget_int]
  have hw1 : 1 ≤ w := by omega
  have hw128 : w ≤ 128 := by omega
  apply BitVec.eq_of_toNat_eq
  have hk : ((w : Int) - 1).toNat - 0 + 1 = w := by omega
  rw [BitVec.toNat_setWidth, extractLsb_toNat', hk, Janus.Arm64.State.getV, ← hzv n hn, BitVec.toNat_ofNat]
  have hd : 2 ^ w ∣ 2 ^ 128 := Nat.pow_dvd_pow 2 hw128
  rw [Nat.mod_mod_of_dvd _ hd, Nat.pow_zero, Nat.div_one, Nat.mod_mod]

theorem run_FPCR_read {js : Janus.Arm64.State} {s : SState} (h : FPRel js s) :
    (FPCR_read ()).run s = .ok (js.fpcr.setWidth 64) s := by
  simp only [FPCR_read, __get_FPCR, run_bind, run_pure, run_readReg h.fpcr, impdef_fp_io, impdef_fp_dz,
    impdef_fp_of, impdef_fp_uf, impdef_fp_ix, impdef_fp_id, impdef_fp_len, Mk_FPCR_Type, Mk_FPCRType,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hk := h.fpcrRes0
  have hl : js.fpcr.toNat < 2 ^ 32 := js.fpcr.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp only [fpcrKeep] at hk
  rw [Nat.mod_eq_of_lt (show js.fpcr.toNat < 2 ^ 64 by omega),
    show 2 ^ 64 - 1 - 18446744073575350520 % 2 ^ 64 = 134201095 by decide]
  exact hk

end JanusASL.Proofs
