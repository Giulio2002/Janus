import JanusASL.Proofs.LdSt
import JanusASL.Proofs.LdStDecode
import JanusASL.Proofs.JanusDecode

/-! # Proved: LDR/STR (unsigned immediate), the general-register forms

`size 111 0 01 opc imm12 Rn Rt` with a valid `size`/`opc` pair (not PRFM): from related states,
under `LinuxEL0Config` and `UserMapped` (Mem.lean), whenever Janus steps the word, the ASL step
completes with `Janus_OK` in a related state (registers and memory). -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_dec_uimm_0_0 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_STORE Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 0) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_0_1 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 0) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_0_2 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 2#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 0) false 64 false true Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_0_3 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 3#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 0) false 32 false true Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_1_0 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_STORE Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 1) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_1_1 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 1) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_1_2 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 2#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 1) false 64 false true Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_1_3 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 3#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 1) false 32 false true Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_2_0 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_STORE Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 2) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_2_1 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 2) false 32 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_2_2 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 2#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 2) false 64 false true Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_3_0 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 0#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_STORE Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 3) false 64 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl

theorem run_dec_uimm_3_1 (Rt Rn : BitVec 5) (imm12 : BitVec 12) (st : SState) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned Rt Rn imm12 1#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_LOAD Rn.toNat false
        (Sail.BitVec.zeroExtend imm12 64 <<< 3) false 64 false false Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
open Janus.Arm64 in
theorem decode_ldstUImm {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 1) (hv : validSizeOpc (bits w 31 30) (bits w 23 22) = true)
    (hnp : ¬(bits w 31 30 = 3 ∧ bits w 23 22 = 2)) :
    decode w = some (.ldstUImm (bits w 31 30) (bits w 23 22) (bits w 21 10) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = true := by simp only [bit_def]; simp; omega
  have e6 : (decide (bits w 31 30 = 3) && decide (bits w 23 22 = 2)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, hv, Bool.false_eq_true, ite_false, ite_true,
    Bool.not_true]
  simp

theorem uimm_offset {w : Nat} (hw : w < 2 ^ 32) (size : Nat) (hs : size < 4) :
    Sail.BitVec.zeroExtend (fld w 10 12) 64 <<< size = BitVec.ofNat 64 (Janus.Arm64.bits w 21 10 * 2 ^ size) := by
  apply BitVec.eq_of_toNat_eq
  rw [bits_eq_fld w 21 10 hw, show 21 + 1 - 10 = 12 from rfl]
  have := fld_lt w 10 12
  have : (fld w 10 12).toNat * 2 ^ size < 2 ^ 64 := by
    have : 2 ^ size ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    have : (fld w 10 12).toNat * 2 ^ size ≤ (fld w 10 12).toNat * 2 ^ 3 := Nat.mul_le_mul_left _ this
    omega
  simp [Sail.BitVec.zeroExtend, Nat.shiftLeft_eq]
  try omega

set_option maxHeartbeats 16000000 in
/-- One `size`/`opc` combination of the class, given its decode chain. -/
theorem uimm_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 1) {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s) {size opc ds rs : Nat} {k : Int} {sgn : Bool} {mem : MemOp}
    (hs3 : (w / 2 ^ 30) % 4 = size) (ho : (w / 2 ^ 22) % 4 = opc)
    (hv : Janus.Arm64.validSizeOpc size opc = true) (hnp : ¬(size = 3 ∧ opc = 2))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds mem (fld w 5 5).toNat false
          (Sail.BitVec.zeroExtend (fld w 10 12) 64 <<< size) false rs false sgn (fld w 0 5).toNat
          ((fld w 5 5).toNat != 31) false false).run (st.set .SEE k))
    (hkind : (mem = .MemOp_LOAD ∧ LoadCase size opc ds rs sgn) ∨ (mem = .MemOp_STORE ∧ opc = 0 ∧ StoreCase size ds))
    (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hb31 : Janus.Arm64.bits w 31 30 = size := by simp only [bits_def]; omega
  have hb23 : Janus.Arm64.bits w 23 22 = opc := by simp only [bits_def]; omega
  rw [Janus.Arm64.step_of_decode (decode_ldstUImm hw h0 h1 h2 (by rw [hb31, hb23]; exact hv)
    (by rw [hb31, hb23]; exact hnp)), hb31, hb23] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
  cases hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hsz4 : size < 4 := by omega
  obtain ⟨hR, hM, hC, hT⟩ := entry_facts h hm hc w k
  have hpc := memIndexed_pc hx
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds mem (Janus.Arm64.bits w 9 5) false
          (BitVec.ofNat 64 (Janus.Arm64.bits w 21 10 * 2 ^ size)) false rs false sgn (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w k) := by
    rw [run_DecodeA64_LS hw (by omega) (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, uimm_offset hw size hsz4]
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  rcases hkind with ⟨rfl, hcase⟩ | ⟨rfl, rfl, hcase⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_load hR hM hC hU hT hcase hn32 ht32 _ false false _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_store (rs := rs) hR hM hC hU hT hcase hn32 ht32 _ false false _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

/-- **LDR/STR (unsigned immediate), general registers**: for every word `size 111 0 01 opc imm12 Rn Rt`
with a valid `size`/`opc` (not PRFM) and every related pair of states under `LinuxEL0Config` and
`UserMapped`, whenever Janus steps the word the generated ASL step completes in a related state,
with Janus' memory related to the ASL's. -/
theorem ldstUImm_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 1)
    (hv : Janus.Arm64.validSizeOpc ((w / 2 ^ 30) % 4) ((w / 2 ^ 22) % 4) = true)
    (hnp : ¬((w / 2 ^ 30) % 4 = 3 ∧ (w / 2 ^ 22) % 4 = 2))
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e1 | e1 | e1 | e1 <;>
  rcases (show (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1 ∨ (w / 2 ^ 22) % 4 = 2 ∨ (w / 2 ^ 22) % 4 = 3 by omega)
    with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hv hnp
  · -- size 0, opc 0
    refine uimm_case (k := 651) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_uimm_0_0 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_0_0 _ _ _ _
  · -- size 0, opc 1
    refine uimm_case (k := 633) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_0_1 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_0_1 _ _ _ _
  · -- size 0, opc 2
    refine uimm_case (k := 639) (ds := 8) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_0_2 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_0_2 _ _ _ _
  · -- size 0, opc 3
    refine uimm_case (k := 639) (ds := 8) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_0_3 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_0_3 _ _ _ _
  · -- size 1, opc 0
    refine uimm_case (k := 654) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_uimm_1_0 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_1_0 _ _ _ _
  · -- size 1, opc 1
    refine uimm_case (k := 636) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_1_1 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_1_1 _ _ _ _
  · -- size 1, opc 2
    refine uimm_case (k := 642) (ds := 16) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_1_2 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_1_2 _ _ _ _
  · -- size 1, opc 3
    refine uimm_case (k := 642) (ds := 16) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_1_3 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_1_3 _ _ _ _
  · -- size 2, opc 0
    refine uimm_case (k := 648) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_uimm_2_0 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_2_0 _ _ _ _
  · -- size 2, opc 1
    refine uimm_case (k := 630) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_2_1 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_2_1 _ _ _ _
  · -- size 2, opc 2
    refine uimm_case (k := 645) (ds := 32) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_2_2 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_2_2 _ _ _ _
  · exact absurd hv (by decide)
  · -- size 3, opc 0
    refine uimm_case (k := 648) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_uimm_3_0 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_3_0 _ _ _ _
  · -- size 3, opc 1
    refine uimm_case (k := 630) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h hm hc hU e1 e2 hv hnp
      (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_uimm_3_1 hw h0 h1 h2 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_uimm_3_1 _ _ _ _
  · exact absurd ⟨rfl, rfl⟩ hnp
  · exact absurd hv (by decide)

end JanusASL.Proofs
