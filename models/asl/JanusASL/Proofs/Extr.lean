import JanusASL.Proofs.MoveWide
import JanusASL.Proofs.AddSubShifted

/-! # Proved: EXTR, the whole encoding class

Words `sf 00 100111 N 0 Rm imms Rn Rd` (bits 30:21 = `00100111N0`) that Janus decodes: `N = sf`,
`imms < 32` when `sf = 0`. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem extr_eq {N : Nat} (x y : BitVec N) (l : Nat) (hl : l < N) :
    BitVec.setWidth N (Sail.BitVec.extractLsb (BitVec.setWidth (2 * N) (x ++ y)) (((l : Int) + N - 1).toNat) l) =
      (x ++ y).extractLsb' l N := by
  apply BitVec.eq_of_toNat_eq
  have hk : ((l : Int) + N - 1).toNat - l + 1 = N := by omega
  have hlt : (x ++ y).toNat < 2 ^ (2 * N) := by
    have := (x ++ y).isLt; exact Nat.lt_of_lt_of_eq this (by rw [show N + N = 2 * N by omega])
  simp only [Sail.BitVec.extractLsb, BitVec.toNat_setWidth, BitVec.extractLsb_toNat, BitVec.extractLsb'_toNat,
    Nat.mod_eq_of_lt hlt, hk, Nat.mod_mod]

set_option maxHeartbeats 4000000 in
theorem run_execute_extr {js : Janus.Arm64.State} {s : SState} (h : Rel js s) {N : Nat}
    (hN : N = 32 ∨ N = 64) {d m n l : Nat} (hd : d < 32) (hm : m < 32) (hn : n < 32) (hl : l < N) :
    ∃ s', (execute_aarch64_instrs_integer_ins_ext_extract_immediate d N l m n).run s = .ok () s' ∧
      Rel (Janus.Arm64.execExtr N js m l n d) s' ∧ Frame s s' := by
  obtain ⟨s', hs', hr, hf⟩ := run_X_set_rel h hd hN ((js.getX N n ++ js.getX N m).extractLsb' l N)
  refine ⟨s', ?_, by simpa [Janus.Arm64.execExtr] using hr, hf⟩
  have ha : ((((l : Int) + (N : Int)) - 1) <b (2 * (N : Int))) = true := by simp; omega
  simp only [execute_aarch64_instrs_integer_ins_ext_extract_immediate, run_bind, run_X_read_rel h hn hN,
    run_X_read_rel h hm hN, run_sail_assert_of ha, run_pure, extr_eq _ _ l hl]
  exact hs'

set_option maxHeartbeats 8000000 in
/-- `__DecodeA64_DataProcImm` on its encoding class reaches clause SEE 206 (`decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate`). -/
theorem run_DataProcImm_extr {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 23) % 64 = 39) (h1 : (w / 2 ^ 29) % 4 = 0) (h2 : (w / 2 ^ 21) % 2 = 0) {s : SState} (hs : s.regs.get? .SEE = some (-1))
    (pc : Int) :
    (__DecodeA64_DataProcImm pc (BitVec.ofNat 32 w)).run s =
      (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate (fld w 0 5) (fld w 5 5) (fld w 10 6) (fld w 16 5) (fld w 22 1) (fld w 31 1)).run (s.set .SEE 206) := by
  have f0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (34#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (98#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f2 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (162#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f3 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (226#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f4 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 31 22 == (582#10 : BitVec 10)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f5 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f6 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 28 24 == (16#5 : BitVec 5)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f7 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (36#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f8 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (228#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f9 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (164#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f10 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (100#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f11 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (102#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f12 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (38#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have f13 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (166#8 : BitVec 8)) = false := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_false (by simp; omega)
  have t14_0 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 30 23 == (39#8 : BitVec 8)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  have t14_1 : (Sail.BitVec.extractLsb (BitVec.ofNat 32 w) 21 21 == (0#1 : BitVec 1)) = true := by
    rw [extractLsb_ofNat32 _ _ _ (by decide) (by decide)]; exact ofNat_beq_true (by simp; omega)
  rw [__DecodeA64_DataProcImm]
  simp only [run_bind, f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, t14_0, t14_1, Bool.and_false, Bool.false_and, Bool.and_true, andM, toBool, run_pure,
    run_readReg hs, Bool.false_eq_true, ite_false, decide_true, ite_true, run_writeReg,
    show ((-1 : Int) < 206) = True from by decide]
  all_goals rfl

theorem run_decode_extr (Rd Rn : BitVec 5) (imms : BitVec 6) (Rm : BitVec 5) (Nb sf : BitVec 1)
    (h1 : (Nb != sf) = false) (h2 : (sf == 0#1 && (Sail.BitVec.access imms 5 == 1#1)) = false) (s : SState) :
    (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm Nb sf).run s =
      (execute_aarch64_instrs_integer_ins_ext_extract_immediate Rd.toNat (if sf == 1#1 then 64 else 32)
        imms.toNat Rm.toNat Rn.toNat).run s := by
  unfold decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate
  simp only [run_bind, h1, h2, Bool.false_eq_true, ite_false, run_pure]

theorem decode_extr_class {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100111)
    (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) :
    Janus.Arm64.decode w = some (.extr (Janus.Arm64.bit w 31) (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 20 16)
      (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 9 5) (Janus.Arm64.bits w 4 0)) := by
  have a1 : ¬ w ≥ 2 ^ 32 := by omega
  have a2 : Janus.Arm64.bits w 28 25 / 2 = 0b100 := by simp only [bits_def]; omega
  have a3 : Janus.Arm64.bits w 25 23 = 0b111 := by simp only [bits_def]; omega
  have a4 : (decide (Janus.Arm64.bits w 30 29 ≠ 0) || Janus.Arm64.bit w 21) = false := by
    simp only [bits_def, bit_def]; simp; omega
  have a5 : (Janus.Arm64.bit w 31 != Janus.Arm64.bit w 22) = false := by
    simp only [bit_def]; rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with e | e <;>
      simp [e] <;> omega
  have a6 : (!Janus.Arm64.bit w 31 && decide (Janus.Arm64.bits w 15 10 ≥ 32)) = false := by
    simp only [bits_def, bit_def]; rcases hsf with e | e <;> simp [e] <;> omega
  simp only [Janus.Arm64.decode, a1, a2, ite_false, ite_true, Janus.Arm64.decodeDPImm, a3, a4, a5, a6]
  simp

set_option maxHeartbeats 8000000 in
theorem asl_extr {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100111)
    (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (pc : Int) :
    ∃ s2, (__DecodeA64 pc (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2 ∧
      Rel (Janus.Arm64.execExtr (if fld w 31 1 == 1#1 then 64 else 32) js
        (fld w 16 5).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat) s2 ∧
      (s2.regs.get? .__BranchTaken = some false ∧ CfgFrame s s2) := by
  rw [run_DecodeA64_DPImm hw (by omega)]
  have e1 : (fld w 22 1 != fld w 31 1) = false := by
    have : fld w 22 1 = fld w 31 1 := by apply BitVec.eq_of_toNat_eq; rw [fld_toNat _ _ _ hw, fld_toNat _ _ _ hw]; simpa using hN.symm
    rw [this]; simp
  have hl : (fld w 10 6).toNat < (if fld w 31 1 == 1#1 then 64 else 32) := by
    have := fld_lt w 10 6
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, e'⟩
    · rw [e]; simp; omega
    · rw [e]; simp; rcases hsf with x | x
      · omega
      · rw [fld_toNat w 10 6 hw]; omega
  have e2 : (fld w 31 1 == 0#1 && (Sail.BitVec.access (fld w 10 6) 5 == 1#1)) = false := by
    rcases fld_sf_cases hw with ⟨e, _⟩ | ⟨e, e'⟩
    · rw [e]; simp
    · rcases hsf with x | x
      · omega
      · have hlt : (fld w 10 6).toNat < 32 := by rw [fld_toNat w 10 6 hw]; omega
        have : Sail.BitVec.access (fld w 10 6) 5 = 0#1 := by
          generalize fld w 10 6 = v at hlt; revert v; decide
        rw [this]; simp
  rw [run_DataProcImm_extr hw hc h0 h21 (see_entry _ _), run_decode_extr _ _ _ _ _ _ e1 e2]
  obtain ⟨s2, hrun, hrel, hfr⟩ := run_execute_extr (h.entry (BitVec.ofNat 32 w) 206) (width_cases w)
    (fld_lt w 0 5) (fld_lt w 16 5) (fld_lt w 5 5) hl
  exact ⟨s2, hrun, hrel, bt_cfg_after _ _ hfr⟩

theorem extr_agree_f {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100111)
    (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') ∧ FPFrame s s' := by
  let F : Nat → Janus.Arm64.State := fun N => Janus.Arm64.execExtr N js
    (fld w 16 5).toNat (fld w 10 6).toNat (fld w 5 5).toNat (fld w 0 5).toNat
  have hspec : ∀ N, (F N).pc = js.pc := by
    intro N; simp [F, Janus.Arm64.execExtr, Janus.Arm64.State.setX, Janus.Arm64.State.writeZR]; split <;> rfl
  obtain ⟨s2, hrun, hrel, hbt⟩ := asl_extr hw hc h0 h21 hN hsf h (js.pc.toNat : Int)
  have e : F (if fld w 31 1 == 1#1 then 64 else 32) = if fld w 31 1 == 1#1 then F 64 else F 32 := by
    split <;> rfl
  have hrel' : Rel (if fld w 31 1 == 1#1 then F 64 else F 32) s2 := e ▸ hrel
  refine step_agree_f h ⟨s2, hrun, hrel', hbt⟩ (by split <;> exact hspec _) ?_
  rw [Janus.Arm64.step_of_decode (decode_extr_class hw hc h0 h21 hN hsf)]
  simp only [Janus.Arm64.exec, ← fld_bit w 31 hw,
    bits_eq_fld w 20 16 hw, bits_eq_fld w 15 10 hw, bits_eq_fld w 9 5 hw, bits_eq_fld w 4 0 hw]
  split <;> simp_all [Janus.Arm64.State.next, F]

/-- **EXTR**: for every word of the encoding class that Janus decodes and every related pair of
states, Janus' `step` and the generated ASL agree. -/
theorem extr_agree {w : Nat} (hw : w < 2 ^ 32) (hc : (w / 2 ^ 23) % 64 = 0b100111)
    (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32)
    {js : Janus.Arm64.State} {s : SState} (h : Rel js s) :
    ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s') := by
  obtain ⟨js', s', h1, h2, h3, h4, -⟩ := extr_agree_f (w := w) (hw := hw) (hc := hc) (h0 := h0) (h21 := h21) (hN := hN) (hsf := hsf) (js := js) (s := s) (h := h)
  exact ⟨js', s', h1, h2, h3, h4⟩

end JanusASL.Proofs
