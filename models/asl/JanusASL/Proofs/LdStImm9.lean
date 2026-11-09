import JanusASL.Proofs.LdStUImm
import JanusASL.Proofs.LdStDecode9

/-! # Proved: LDUR/STUR and LDR/STR (pre- and post-index), the general-register forms

`size 111 0 00 opc 0 imm9 op4 Rn Rt` with `op4` 00 (unscaled), 01 (post-index), 11 (pre-index), a
valid `size`/`opc` (not PRFUM/PRFM) and, with write-back, `Rn ≠ Rt` unless `Rn = 31` (what
Janus decodes). Hypotheses as in LdStUImm.lean. -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset load** (`LDR`/`LDRB`/`LDRH`/`LDRS*`, unsigned offset,
unscaled, pre- and post-index): Janus' `memIndexed`/`memSingle` against the ASL's
`execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal`. -/
theorem run_exec_load_u {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size opc ds rs : Nat}
    {sgn : Bool} (hcase : LoadCase size opc ds rs sgn) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memSingle s size opc rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal ds .MemOp_LOAD rn false offset
      postindex rs false sgn rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ RStep s s' := by
  obtain ⟨hopc, hrs, hdsn, hsz, hds0, hdsrs⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · next base hb =>
  simp only at hj
  split at hj
  · cases hj
  · next js2 hs2 =>
  cases hj
  have hB := run_base h hc hn hb
  generalize hA : (if postindex = true then base else base + offset) = addr at hs2
  obtain ⟨hacc, rfl⟩ := memSingle_load hopc hs2
  obtain ⟨v, hv, hvn⟩ := run_Mem_read hU hf hc hm addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  have hcr := run_CreateAccDescGPR hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  have hval := load_value hcase hdsn v _ (by rw [hvn, hdsn])
  have has : (decide (0 < ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has2 : (decide (0 ≤ ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has3 : decide (ds ≤ rs) = true := by simp; omega
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', hv, has, has2]
  obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht hrs
    (if sgn then Sail.BitVec.signExtend (BitVec.setWidth ds v) rs else Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs)
  have hval' : (if sgn then Sail.BitVec.signExtend (BitVec.setWidth ds v) rs
      else Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs).setWidth 64 = loadVal size opc (js.mem.readLE addr.toNat (2 ^ size)) := by
    rw [← hval]; cases sgn <;> rfl
  simp only [Janus.Arm64.State.setX, hval'] at hr1
  have hc1 := hc.rstep hst1
  cases sgn <;> (try simp only [Bool.false_eq_true, ite_false, ite_true] at hx1) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, hx1]
  all_goals
    cases wback
    · refine ⟨s1, ?_, hr1, ?_, hst1⟩
      · cfg_simp [run_readReg hc1.speInFlight, has3, hx1]
      · simp only [Bool.false_eq_true, ite_false, writeZR_mem]; exact hm.rstep hst1
    · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + offset)
      have hc2 := hc1.rstep hst2
      refine ⟨s2, ?_, hr2, ?_, hst1.trans hst2⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx2, run_readReg hc2.speInFlight, has3, hx1]
      · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst1.trans hst2)

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset store** (`STR`/`STRB`/`STRH`, all immediate forms). -/
theorem run_exec_store_u {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (offset : BitVec 64) (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn offset postindex wback (fun s a => Janus.Arm64.memSingle s size 0 rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal ds .MemOp_STORE rn false offset
      postindex rs false false rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧
      GFrame s s' ∧ (∀ b, ¬ InRegion js.mem b false → s'.mem.get? b = s.mem.get? b) ∧
      s'.cycleCount = s.cycleCount ∧ s'.sailOutput = s.sailOutput := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  unfold Janus.Arm64.memIndexed at hj
  split at hj
  · cases hj
  · next base hb =>
  simp only at hj
  split at hj
  · cases hj
  · next js2 hs2 =>
  cases hj
  have hB := run_base h hc hn hb
  generalize hA : (if postindex = true then base else base + offset) = addr at hs2
  obtain ⟨hacc, rfl⟩ := memSingle_store hs2
  have hX := run_X_read_w h ht hds
  obtain ⟨s1, hv, hst⟩ := run_Mem_set hU hf hc addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc (BitVec.setWidth _ (BitVec.setWidth ds (js.readZR rt)))
  unfold execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  have hcr := run_CreateAccDescGPR hc true tc
  simp only [ite_true] at hcr
  have hA' : (if postindex = false then base + offset else base) = addr := by rw [← hA]; cases postindex <;> rfl
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hA', hX, hv]
  have hr1 := h.mem_update hst.regs (js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat)
  have hreg := accessible_bytes hacc
  have hm1 : MemRel (js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat) s1 := by
    refine hm.store (hdsn ▸ hst) ?_
    simp only [BitVec.toNat_setWidth, hdsn]
    rw [show 2 ^ size * 8 = 8 * 2 ^ size by omega, ← hds8, Nat.mod_mod, Nat.mod_mod]
  have hmo := MStep_of_stored hst (fun i hi => (hreg i (by rw [hdsn] at hi; exact hi)).read)
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  have hg1 : GFrame s s1 := fun r _ _ => by show s1.regs.get? r = s.regs.get? r; rw [hst.regs]
  have hwl : ∀ (d : Nat) (v : BitVec 64), ({ js with mem := js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat }.writeSP d v).mem =
      js.mem.writeLE addr.toNat (2 ^ size) (js.readZR rt).toNat := fun d v => writeSP_mem _ d v
  cases wback
  · refine ⟨s1, ?_, hr1, hm1, hg1, hmo, hst.cycle, hst.out⟩
    cfg_simp [run_readReg hc1.speInFlight]
  · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + offset)
    have hc2 := hc1.rstep hst2
    refine ⟨s2, ?_, hr2, ?_, fun r h1 h2 => (hst2.regs r h1 h2).trans (hg1 r h1 h2), fun b hb => ?_,
      hst2.cycle.trans hst.cycle, hst2.out.trans hst.out⟩
    · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
      cfg_simp [hx2, run_readReg hc2.speInFlight]
    · simp only [ite_true, hwl]; exact hm1.rstep hst2
    · rw [hst2.mem]; exact hmo b hb

theorem run_dec_i9_0_0_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 0#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 8 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_0_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 1#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_0_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 2#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_0_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 3#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false true Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_1_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 0#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 16 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_1_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 1#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_1_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 2#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_1_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 3#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false true Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_2_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 0#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 32 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_2_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 1#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_2_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 2#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_3_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 0#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 64 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 64 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_0_3_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) :
    (decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal Rt Rn imm9 1#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal 64 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false false Rt.toNat
        (Rn.toNat != 31) false false).run st := by
  unfold decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals rfl
theorem run_dec_i9_1_0_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_0_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_0_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 2#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_0_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 3#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 32 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_1_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_1_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_1_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 2#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_1_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 3#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 32 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_2_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_2_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_2_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 2#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_3_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 0#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) true 64 false false Rt.toNat
        true false true).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_1_3_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx Rt Rn imm9 1#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) true 64 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_0_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 0#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_0_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 1#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_0_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 2#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_0_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 3#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 8 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_1_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 0#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_1_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 1#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_1_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 2#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_1_3 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 3#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 16 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_2_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 0#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_2_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 1#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 32 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_2_2 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 2#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 32 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false true Rt.toNat
        true false true).run st := by
  unfold decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_3_0 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 0#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_STORE Rn.toNat false (sign_extend imm9 64) false 64 false false Rt.toNat
        true false true).run st := by
  unfold decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl
theorem run_dec_i9_3_3_1 (Rt Rn : BitVec 5) (imm9 : BitVec 9) (st : SState) (hnt : ¬(Rn.toNat = Rt.toNat ∧ Rn.toNat ≠ 31)) :
    (decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx Rt Rn imm9 1#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx 64 .MemOp_LOAD Rn.toNat false (sign_extend imm9 64) false 64 false false Rt.toNat
        true false true).run st := by
  unfold decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx
  have e2 : ¬(Rn.toNat = Rt.toNat ∧ ¬Rn.toNat = 31) := hnt
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint]
  all_goals (try rw [if_neg e2])
  all_goals (try simp only [run_pure, run_bind, if_neg e2])
  all_goals rfl

open Janus.Arm64 in
theorem decode_ldstImm9 {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hop : (w / 2 ^ 10) % 4 ≠ 2)
    (hv : validSizeOpc (bits w 31 30) (bits w 23 22) = true) (hnp : ¬(bits w 31 30 = 3 ∧ bits w 23 22 = 2))
    (hnt : (w / 2 ^ 10) % 4 ≠ 0 → ¬(bits w 9 5 = bits w 4 0 ∧ bits w 9 5 ≠ 31)) :
    decode w = some (.ldstImm9 (bits w 31 30) (bits w 23 22)
      (if bits w 11 10 = 0 then .unscaled else if bits w 11 10 = 1 then .post else .pre)
      (bits w 20 12) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bit w 21 = false := by simp only [bit_def]; simp; omega
  have e7 : (decide (bits w 31 30 = 3) && decide (bits w 23 22 = 2)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  have e8 : ¬ bits w 11 10 = 2 := by simp only [bits_def]; omega
  have e9 : (decide (bits w 11 10 ≠ 0) && (bits w 9 5 == bits w 4 0) && decide (bits w 9 5 ≠ 31)) = false := by
    have : bits w 11 10 = (w / 2 ^ 10) % 4 := by simp only [bits_def]
    rw [this]
    by_cases hz : (w / 2 ^ 10) % 4 = 0
    · simp [hz]
    · have := hnt hz; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]; omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, hv, e8, e9, Bool.false_eq_true, ite_false,
    ite_true, Bool.not_true, Bool.not_false]
  simp

theorem i9_offset {w : Nat} (hw : w < 2 ^ 32) :
    sign_extend (fld w 12 9) 64 = Janus.Arm64.sext64 9 (Janus.Arm64.bits w 20 12) := by
  have : fld w 12 9 = BitVec.ofNat 9 (Janus.Arm64.bits w 20 12) := by
    apply BitVec.eq_of_toNat_eq; rw [fld_toNat w 12 9 hw, bits_eq_fld w 20 12 hw, fld_toNat w 12 9 hw]; simp
  rw [this]; rfl

set_option maxHeartbeats 16000000 in
/-- One `size`/`opc`/`op4` combination of the imm9 class, given its decode chain. -/
theorem i9u_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0)
    {op4 : Nat} (hop4 : (w / 2 ^ 10) % 4 = op4) (h40 : op4 = 0) {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s) {size opc ds rs : Nat} {k : Int} {sgn : Bool} {mem : MemOp}
    (hs3 : (w / 2 ^ 30) % 4 = size) (ho : (w / 2 ^ 22) % 4 = opc)
    (hv : Janus.Arm64.validSizeOpc size opc = true) (hnp : ¬(size = 3 ∧ opc = 2))
    (hnt : op4 ≠ 0 → ¬(Janus.Arm64.bits w 9 5 = Janus.Arm64.bits w 4 0 ∧ Janus.Arm64.bits w 9 5 ≠ 31))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal ds mem (fld w 5 5).toNat false
          (sign_extend (fld w 12 9) 64) false rs false sgn (fld w 0 5).toNat
          ((fld w 5 5).toNat != 31) false false).run (st.set .SEE k))
    (hkind : (mem = .MemOp_LOAD ∧ LoadCase size opc ds rs sgn) ∨ (mem = .MemOp_STORE ∧ opc = 0 ∧ StoreCase size ds))
    (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hb31 : Janus.Arm64.bits w 31 30 = size := by simp only [bits_def]; omega
  have hb23 : Janus.Arm64.bits w 23 22 = opc := by simp only [bits_def]; omega
  have hb11 : Janus.Arm64.bits w 11 10 = op4 := by simp only [bits_def]; omega
  rw [Janus.Arm64.step_of_decode (decode_ldstImm9 hw h0 h1 h2 h21 (by omega) (by rw [hb31, hb23]; exact hv)
    (by rw [hb31, hb23]; exact hnp) (fun h => hnt (by omega))), hb31, hb23, hb11] at hj
  simp only [Janus.Arm64.exec] at hj
  subst h40; simp only [ite_true] at hj
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
      (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal ds mem (Janus.Arm64.bits w 9 5) false
          (Janus.Arm64.sext64 9 (Janus.Arm64.bits w 20 12)) false rs false sgn (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w k) := by
    rw [run_DecodeA64_LS hw (by omega) (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, i9_offset hw]
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  rcases hkind with ⟨rfl, hcase⟩ | ⟨rfl, rfl, hcase⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_load_u hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_store_u (rs := rs) hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- One `size`/`opc`/`op4` combination of the imm9 class, given its decode chain. -/
theorem i9post_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0)
    (hop4 : (w / 2 ^ 10) % 4 = 1) {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s) {size opc ds rs : Nat} {k : Int} {sgn : Bool} {mem : MemOp}
    (hs3 : (w / 2 ^ 30) % 4 = size) (ho : (w / 2 ^ 22) % 4 = opc)
    (hv : Janus.Arm64.validSizeOpc size opc = true) (hnp : ¬(size = 3 ∧ opc = 2))
    (hnt : 1 ≠ 0 → ¬(Janus.Arm64.bits w 9 5 = Janus.Arm64.bits w 4 0 ∧ Janus.Arm64.bits w 9 5 ≠ 31))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds mem (fld w 5 5).toNat false
          (sign_extend (fld w 12 9) 64) true rs false sgn (fld w 0 5).toNat
          true false true).run (st.set .SEE k))
    (hkind : (mem = .MemOp_LOAD ∧ LoadCase size opc ds rs sgn) ∨ (mem = .MemOp_STORE ∧ opc = 0 ∧ StoreCase size ds))
    (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hb31 : Janus.Arm64.bits w 31 30 = size := by simp only [bits_def]; omega
  have hb23 : Janus.Arm64.bits w 23 22 = opc := by simp only [bits_def]; omega
  have hb11 : Janus.Arm64.bits w 11 10 = 1 := by simp only [bits_def]; omega
  rw [Janus.Arm64.step_of_decode (decode_ldstImm9 hw h0 h1 h2 h21 (by omega) (by rw [hb31, hb23]; exact hv)
    (by rw [hb31, hb23]; exact hnp) (fun h => hnt (by omega))), hb31, hb23, hb11] at hj
  simp only [Janus.Arm64.exec] at hj
  simp only [show (1 = 0) = False from by decide, show (3 = 0) = False from by decide, show (3 = 1) = False from by decide, ite_false, ite_true] at hj
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
          (Janus.Arm64.sext64 9 (Janus.Arm64.bits w 20 12)) true rs false sgn (Janus.Arm64.bits w 4 0)
          true false true).run (entrySt s w k) := by
    rw [run_DecodeA64_LS hw (by omega) (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, i9_offset hw]
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  rcases hkind with ⟨rfl, hcase⟩ | ⟨rfl, rfl, hcase⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_load hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_store (rs := rs) hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

set_option maxHeartbeats 16000000 in
/-- One `size`/`opc`/`op4` combination of the imm9 class, given its decode chain. -/
theorem i9pre_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0)
    (hop4 : (w / 2 ^ 10) % 4 = 3) {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s) {size opc ds rs : Nat} {k : Int} {sgn : Bool} {mem : MemOp}
    (hs3 : (w / 2 ^ 30) % 4 = size) (ho : (w / 2 ^ 22) % 4 = opc)
    (hv : Janus.Arm64.validSizeOpc size opc = true) (hnp : ¬(size = 3 ∧ opc = 2))
    (hnt : 3 ≠ 0 → ¬(Janus.Arm64.bits w 9 5 = Janus.Arm64.bits w 4 0 ∧ Janus.Arm64.bits w 9 5 ≠ 31))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx ds mem (fld w 5 5).toNat false
          (sign_extend (fld w 12 9) 64) false rs false sgn (fld w 0 5).toNat
          true false true).run (st.set .SEE k))
    (hkind : (mem = .MemOp_LOAD ∧ LoadCase size opc ds rs sgn) ∨ (mem = .MemOp_STORE ∧ opc = 0 ∧ StoreCase size ds))
    (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hb31 : Janus.Arm64.bits w 31 30 = size := by simp only [bits_def]; omega
  have hb23 : Janus.Arm64.bits w 23 22 = opc := by simp only [bits_def]; omega
  have hb11 : Janus.Arm64.bits w 11 10 = 3 := by simp only [bits_def]; omega
  rw [Janus.Arm64.step_of_decode (decode_ldstImm9 hw h0 h1 h2 h21 (by omega) (by rw [hb31, hb23]; exact hv)
    (by rw [hb31, hb23]; exact hnp) (fun h => hnt (by omega))), hb31, hb23, hb11] at hj
  simp only [Janus.Arm64.exec] at hj
  simp only [show (1 = 0) = False from by decide, show (3 = 0) = False from by decide, show (3 = 1) = False from by decide, ite_false, ite_true] at hj
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
          (Janus.Arm64.sext64 9 (Janus.Arm64.bits w 20 12)) false rs false sgn (Janus.Arm64.bits w 4 0)
          true false true).run (entrySt s w k) := by
    rw [run_DecodeA64_LS hw (by omega) (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, i9_offset hw]
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  rcases hkind with ⟨rfl, hcase⟩ | ⟨rfl, rfl, hcase⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_load hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_store (rs := rs) hR hM hC hU hT hcase hn32 ht32 _ _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

/-- **LDUR/STUR and LDR/STR (pre- and post-index), general registers**: for every word
`size 111 0 00 opc 0 imm9 op4 Rn Rt` with `op4 ∈ {00, 01, 11}`, a valid `size`/`opc` (not PRFUM/PRFM)
and, with write-back, `Rn ≠ Rt` or `Rn = 31`, and every related pair of states under
`LinuxEL0Config` and `UserMapped`, whenever Janus steps the word the generated ASL step completes in
a related state, with Janus' memory related to the ASL's. -/
theorem ldstImm9_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0) (hop : (w / 2 ^ 10) % 4 ≠ 2)
    (hv : Janus.Arm64.validSizeOpc ((w / 2 ^ 30) % 4) ((w / 2 ^ 22) % 4) = true)
    (hnp : ¬((w / 2 ^ 30) % 4 = 3 ∧ (w / 2 ^ 22) % 4 = 2))
    (hnt : (w / 2 ^ 10) % 4 ≠ 0 → ¬((w / 2 ^ 5) % 32 = w % 32 ∧ (w / 2 ^ 5) % 32 ≠ 31))
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hrn' : (fld w 5 5).toNat = (w / 2 ^ 5) % 32 := by rw [fld_toNat w 5 5 hw]
  have hrt' : (fld w 0 5).toNat = w % 32 := by rw [fld_toNat w 0 5 hw]; simp
  have hnt' : ∀ op4, (w / 2 ^ 10) % 4 = op4 → op4 ≠ 0 →
      ¬(Janus.Arm64.bits w 9 5 = Janus.Arm64.bits w 4 0 ∧ Janus.Arm64.bits w 9 5 ≠ 31) := by
    intro op4 e h0'; simp only [bits_def]; have := hnt (by omega); simp at this ⊢; omega
  have e3' : (w / 2 ^ 10) % 4 = 0 ∨ (w / 2 ^ 10) % 4 = 1 ∨ (w / 2 ^ 10) % 4 = 3 := by omega
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e1 | e1 | e1 | e1 <;>
  rcases (show (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1 ∨ (w / 2 ^ 22) % 4 = 2 ∨ (w / 2 ^ 22) % 4 = 3 by omega)
    with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hv hnp
  · -- size 0, opc 0
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 688) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_0_0_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_0_0 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 649) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_1_0_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_0_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 650) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_3_0_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_0_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 0, opc 1
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 681) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_0_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_0_1 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 631) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_0_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_0_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 632) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_0_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_0_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 0, opc 2
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 683) (ds := 8) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_0_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_0_2 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 637) (ds := 8) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_0_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_0_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 638) (ds := 8) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_0_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_0_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 0, opc 3
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 683) (ds := 8) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_0_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_0_3 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 637) (ds := 8) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_0_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_0_3 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 638) (ds := 8) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_0_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_0_3 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 1, opc 0
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 689) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_0_1_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_1_0 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 652) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_1_1_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_1_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 653) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_3_1_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_1_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 1, opc 1
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 682) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_1_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_1_1 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 634) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_1_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_1_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 635) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_1_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_1_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 1, opc 2
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 684) (ds := 16) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_1_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_1_2 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 640) (ds := 16) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_1_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_1_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 641) (ds := 16) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_1_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_1_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 1, opc 3
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 684) (ds := 16) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_1_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_1_3 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 640) (ds := 16) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_1_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_1_3 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 641) (ds := 16) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_1_3 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_1_3 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 2, opc 0
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 687) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_0_2_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_2_0 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 646) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_1_2_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_2_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 647) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_3_2_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_2_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 2, opc 1
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 680) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_2_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_2_1 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 628) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_2_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_2_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 629) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_2_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_2_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 2, opc 2
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 685) (ds := 32) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_2_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_2_2 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 643) (ds := 32) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_2_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_2_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 644) (ds := 32) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_2_2 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_2_2 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · exact absurd hv (by decide)
  · -- size 3, opc 0
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 687) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_0_3_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_3_0 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 646) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_1_3_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_3_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 647) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
      rw [run_LS_i9_3_3_0 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_3_0 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · -- size 3, opc 1
    rcases e3' with e3 | e3 | e3
    · -- op4 0
      refine i9u_case (k := 680) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 rfl h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_0_3_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_0_3_1 _ _ _ _
    · -- op4 1
      refine i9post_case (k := 628) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_1_3_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_1_3_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
    · -- op4 3
      refine i9pre_case (k := 629) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 e3 h hm hc hU e1 e2 hv hnp
        (hnt' _ e3) (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
      rw [run_LS_i9_3_3_1 hw h0 h1 h2 h21 (by omega) (by omega) (by omega) hst,
        show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
      exact run_dec_i9_3_3_1 _ _ _ _ (by rw [hrn', hrt']; exact hnt (by omega))
  · exact absurd ⟨rfl, rfl⟩ hnp
  · exact absurd hv (by decide)

end JanusASL.Proofs
