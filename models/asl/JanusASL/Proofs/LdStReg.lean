import JanusASL.Proofs.LdStImm9
import JanusASL.Proofs.AddSubExt
import JanusASL.Proofs.LdStDecodeR

/-! # Proved: LDR/STR (register offset), the general-register forms -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset load** (`LDR`/`LDRB`/`LDRH`/`LDRS*`, unsigned offset,
unscaled, pre- and post-index): Janus' `memIndexed`/`memSingle` against the ASL's
`execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx`. -/
theorem run_exec_load_r {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size opc ds rs : Nat}
    {sgn : Bool} (hcase : LoadCase size opc ds rs sgn) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    {rm : Nat} (hrm : rm < 32) (ext : Janus.Arm64.ExtendType) {sh : Nat} (hsh : sh ≤ 4)
    (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn (Janus.Arm64.extendReg 64 (js.readZR rm) ext sh) postindex wback (fun s a => Janus.Arm64.memSingle s size opc rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_register ds (aslExtendType ext) rm .MemOp_LOAD rn false
      postindex rs false sh sgn rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧ RStep s s' := by
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
  generalize hA : (if postindex = true then base else base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh) = addr at hs2
  obtain ⟨hacc, rfl⟩ := memSingle_load hopc hs2
  obtain ⟨v, hv, hvn⟩ := run_Mem_read hU hf hc hm addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc
  unfold execute_aarch64_instrs_memory_single_general_register
  have hER := run_ExtendReg h hrm (Or.inr rfl) ext hsh
  have hcr := run_CreateAccDescGPR hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have hA' : (if postindex = false then base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh else base) = addr := by rw [← hA]; cases postindex <;> rfl
  have hval := load_value hcase hdsn v _ (by rw [hvn, hdsn])
  have has : (decide (0 < ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has2 : (decide (0 ≤ ds) && decide (ds ≤ rs)) = true := by simp; omega
  have has3 : decide (ds ≤ rs) = true := by simp; omega
  cfg_simp [hER, run_readReg hp, he, EL0, hcr, hB, hA', hv, has, has2]
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
    · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh)
      have hc2 := hc1.rstep hst2
      refine ⟨s2, ?_, hr2, ?_, hst1.trans hst2⟩
      · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
        cfg_simp [hx2, run_readReg hc2.speInFlight, has3, hx1]
      · simp only [ite_true, writeSP_mem, writeZR_mem]; exact hm.rstep (hst1.trans hst2)

set_option maxHeartbeats 16000000 in
/-- **The single-register immediate-offset store** (`STR`/`STRB`/`STRH`, all immediate forms). -/
theorem run_exec_store_r {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    {rm : Nat} (hrm : rm < 32) (ext : Janus.Arm64.ExtendType) {sh : Nat} (hsh : sh ≤ 4)
    (postindex wback tc : Bool)
    (hj : Janus.Arm64.memIndexed js rn (Janus.Arm64.extendReg 64 (js.readZR rm) ext sh) postindex wback (fun s a => Janus.Arm64.memSingle s size 0 rt a) =
      .ok js1) :
    ∃ s', (execute_aarch64_instrs_memory_single_general_register ds (aslExtendType ext) rm .MemOp_STORE rn false
      postindex rs false sh false rt tc false wback).run s = .ok () s' ∧ Rel js1 s' ∧ MemRel js1.mem s' ∧
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
  generalize hA : (if postindex = true then base else base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh) = addr at hs2
  obtain ⟨hacc, rfl⟩ := memSingle_store hs2
  have hX := run_X_read_w h ht hds
  obtain ⟨s1, hv, hst⟩ := run_Mem_set hU hf hc addr (Int.ediv (ds : Int) 8).toNat (by rw [hdsn]; exact hsz)
    (by rw [hdsn]; exact hacc) tc (BitVec.setWidth _ (BitVec.setWidth ds (js.readZR rt)))
  unfold execute_aarch64_instrs_memory_single_general_register
  have hER := run_ExtendReg h hrm (Or.inr rfl) ext hsh
  have hcr := run_CreateAccDescGPR hc true tc
  simp only [ite_true] at hcr
  have hA' : (if postindex = false then base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh else base) = addr := by rw [← hA]; cases postindex <;> rfl
  cfg_simp [hER, run_readReg hp, he, EL0, hcr, hB, hA', hX, hv]
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
  · obtain ⟨s2, hx2, hr2, hst2⟩ := run_writeback hr1 hc1 hn (base + Janus.Arm64.extendReg 64 (js.readZR rm) ext sh)
    have hc2 := hc1.rstep hst2
    refine ⟨s2, ?_, hr2, ?_, fun r h1 h2 => (hst2.regs r h1 h2).trans (hg1 r h1 h2), fun b hb => ?_,
      hst2.cycle.trans hst.cycle, hst2.out.trans hst.out⟩
    · cases postindex <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hA <;> subst hA <;>
      cfg_simp [hx2, run_readReg hc2.speInFlight]
    · simp only [ite_true, hwl]; exact hm1.rstep hst2
    · rw [hst2.mem]; exact hmo b hb

theorem run_dec_reg_0_0 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_strb_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 0#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 8 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_STORE Rn.toNat false false 32 false (if S == 1#1 then 0 else 0) false Rt.toNat true false false).run st := by
  unfold decode_strb_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_0_1 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 1#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 8 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 32 false (if S == 1#1 then 0 else 0) false Rt.toNat true false false).run st := by
  unfold decode_ldrb_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_0_2 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 2#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 8 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 64 false (if S == 1#1 then 0 else 0) true Rt.toNat true false false).run st := by
  unfold decode_ldrsb_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_0_3 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrsb_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 3#2 0#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 8 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 32 false (if S == 1#1 then 0 else 0) true Rt.toNat true false false).run st := by
  unfold decode_ldrsb_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_1_0 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_strh_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 0#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 16 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_STORE Rn.toNat false false 32 false (if S == 1#1 then 1 else 0) false Rt.toNat true false false).run st := by
  unfold decode_strh_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_1_1 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrh_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 1#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 16 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 32 false (if S == 1#1 then 1 else 0) false Rt.toNat true false false).run st := by
  unfold decode_ldrh_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_1_2 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 2#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 16 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 64 false (if S == 1#1 then 1 else 0) true Rt.toNat true false false).run st := by
  unfold decode_ldrsh_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_1_3 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrsh_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 3#2 1#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 16 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 32 false (if S == 1#1 then 1 else 0) true Rt.toNat true false false).run st := by
  unfold decode_ldrsh_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_2_0 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 0#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 32 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_STORE Rn.toNat false false 32 false (if S == 1#1 then 2 else 0) false Rt.toNat true false false).run st := by
  unfold decode_str_reg_gen_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_2_1 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 1#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 32 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 32 false (if S == 1#1 then 2 else 0) false Rt.toNat true false false).run st := by
  unfold decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_2_2 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldrsw_reg_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 2#2 2#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 32 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 64 false (if S == 1#1 then 2 else 0) true Rt.toNat true false false).run st := by
  unfold decode_ldrsw_reg_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_3_0 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_str_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 0#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 64 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_STORE Rn.toNat false false 64 false (if S == 1#1 then 3 else 0) false Rt.toNat true false false).run st := by
  unfold decode_str_reg_gen_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

theorem run_dec_reg_3_1 (Rt Rn Rm : BitVec 5) (S : BitVec 1) (opt : BitVec 3)
    (hopt : Sail.BitVec.access opt 1 = 1#1) (st : SState) :
    (decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register Rt Rn S opt Rm 1#2 3#2).run st =
      (execute_aarch64_instrs_memory_single_general_register 64 (aslExtendType (Janus.Arm64.ExtendType.ofBits opt.toNat))
        Rm.toNat .MemOp_LOAD Rn.toNat false false 64 false (if S == 1#1 then 3 else 0) false Rt.toNat true false false).run st := by
  unfold decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register
  cfg_simp [undefined_MemOp, run_internal_pick, undefined_Constraint, hopt, run_DecodeRegExtend]
  all_goals first | rfl | (cases S using BitVec.casesOn; rfl) | skip

open Janus.Arm64 in
theorem decode_ldstReg {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2)
    (hopt : (w / 2 ^ 14) % 2 = 1)
    (hv : validSizeOpc (bits w 31 30) (bits w 23 22) = true) (hnp : ¬(bits w 31 30 = 3 ∧ bits w 23 22 = 2)) :
    decode w = some (.ldstReg (bits w 31 30) (bits w 23 22) (bits w 20 16) (ExtendType.ofBits (bits w 15 13))
      (bit w 12) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bit w 21 = true := by simp only [bit_def]; simp; omega
  have e7 : (decide (bits w 31 30 = 3) && decide (bits w 23 22 = 2)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
  have e8 : bits w 11 10 = 2 := by simp only [bits_def]; omega
  have e9 : ¬ (bits w 15 13 / 2 % 2 = 0) := by simp only [bits_def]; omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, hv, e8, e9, Bool.false_eq_true, ite_false,
    ite_true, Bool.not_true, Bool.not_false]
  simp

set_option maxHeartbeats 16000000 in
/-- One `size`/`opc` combination of the register-offset class, given its decode chain. -/
theorem reg_case {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2)
    (hopt : (w / 2 ^ 14) % 2 = 1)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s) {size opc ds rs : Nat} {k : Int} {sgn : Bool} {mem : MemOp}
    (hs3 : (w / 2 ^ 30) % 4 = size) (ho : (w / 2 ^ 22) % 4 = opc)
    (hv : Janus.Arm64.validSizeOpc size opc = true) (hnp : ¬(size = 3 ∧ opc = 2))
    (hchain : ∀ st : SState, st.regs.get? .SEE = some (-1) →
      (__DecodeA64_LoadStore (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run st =
        (execute_aarch64_instrs_memory_single_general_register ds
          (aslExtendType (Janus.Arm64.ExtendType.ofBits (fld w 13 3).toNat)) (fld w 16 5).toNat mem
          (fld w 5 5).toNat false false rs false (if fld w 12 1 == 1#1 then size else 0) sgn (fld w 0 5).toNat
          true false false).run (st.set .SEE k))
    (hkind : (mem = .MemOp_LOAD ∧ LoadCase size opc ds rs sgn) ∨ (mem = .MemOp_STORE ∧ opc = 0 ∧ StoreCase size ds))
    (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hb31 : Janus.Arm64.bits w 31 30 = size := by simp only [bits_def]; omega
  have hb23 : Janus.Arm64.bits w 23 22 = opc := by simp only [bits_def]; omega
  rw [Janus.Arm64.step_of_decode (decode_ldstReg hw h0 h1 h2 h21 h10 hopt (by rw [hb31, hb23]; exact hv)
    (by rw [hb31, hb23]; exact hnp)), hb31, hb23] at hj
  simp only [Janus.Arm64.exec] at hj
  split at hj
  · cases hj
  · next js1 hx =>
  cases hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hrm : (fld w 16 5).toNat = Janus.Arm64.bits w 20 16 := (bits_eq_fld w 20 16 hw).symm
  have hop : (fld w 13 3).toNat = Janus.Arm64.bits w 15 13 := (bits_eq_fld w 15 13 hw).symm
  have hS : (if fld w 12 1 == 1#1 then size else 0) = (if Janus.Arm64.bit w 12 then size else 0) := by
    rw [fld_bit w 12 hw]
  obtain ⟨hR, hM, hC, hT⟩ := entry_facts h hm hc w k
  have hpc := memIndexed_pc hx
  have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
      (execute_aarch64_instrs_memory_single_general_register ds
          (aslExtendType (Janus.Arm64.ExtendType.ofBits (Janus.Arm64.bits w 15 13))) (Janus.Arm64.bits w 20 16) mem
          (Janus.Arm64.bits w 9 5) false false rs false (if Janus.Arm64.bit w 12 then size else 0) sgn
          (Janus.Arm64.bits w 4 0) true false false).run (entrySt s w k) := by
    rw [run_DecodeA64_LS hw (by omega) (by omega) (by omega), hchain _ (see_entry s _), hrn, hrt, hrm, hop, hS]
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hm32 : Janus.Arm64.bits w 20 16 < 32 := by simp only [bits_def]; omega
  have hsh : (if Janus.Arm64.bit w 12 then size else 0) ≤ 4 := by split <;> omega
  rcases hkind with ⟨rfl, hcase⟩ | ⟨rfl, rfl, hcase⟩
  · obtain ⟨s2, hr2, hrel, hmem, hst⟩ := run_exec_load_r hR hM hC hU hT hcase hn32 ht32 hm32 _ hsh _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · obtain ⟨s2, hr2, hrel, hmem, hg, _⟩ := run_exec_store_r (rs := rs) hR hM hC hU hT hcase hn32 ht32 hm32 _ hsh _ _ _ hx
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := k) (hdec.trans hr2) hrel hg hpc
    exact ⟨_, e1, e2, hmem, e3⟩

theorem access1_of {x : BitVec 3} (h : x.toNat / 2 % 2 = 1) : Sail.BitVec.access x 1 = 1#1 := by
  revert h; revert x; decide

/-- **LDR/STR (register offset), general registers**: for every word
`size 111 0 00 opc 1 Rm option S 10 Rn Rt` with `option<1> = 1`, a valid `size`/`opc` (not PRFM)
and every related pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the
word the generated ASL step completes in a related state, with Janus' memory related to the
ASL's. -/
theorem ldstReg_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 4 = 2)
    (hopt : (w / 2 ^ 14) % 2 = 1)
    (hv : Janus.Arm64.validSizeOpc ((w / 2 ^ 30) % 4) ((w / 2 ^ 22) % 4) = true)
    (hnp : ¬((w / 2 ^ 30) % 4 = 3 ∧ (w / 2 ^ 22) % 4 = 2))
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  have hacc : Sail.BitVec.access (fld w 13 3) 1 = 1#1 := access1_of (by rw [fld_toNat w 13 3 hw]; omega)
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e1 | e1 | e1 | e1 <;>
  rcases (show (w / 2 ^ 22) % 4 = 0 ∨ (w / 2 ^ 22) % 4 = 1 ∨ (w / 2 ^ 22) % 4 = 2 ∨ (w / 2 ^ 22) % 4 = 3 by omega)
    with e2 | e2 | e2 | e2 <;> rw [e1, e2] at hv hnp
  · -- size 0, opc 0
    refine reg_case (k := 663) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_reg_0_0 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_0_0 _ _ _ _ _ hacc _
  · -- size 0, opc 1
    refine reg_case (k := 656) (ds := 8) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_0_1 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_0_1 _ _ _ _ _ hacc _
  · -- size 0, opc 2
    refine reg_case (k := 658) (ds := 8) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_0_2 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_0_2 _ _ _ _ _ hacc _
  · -- size 0, opc 3
    refine reg_case (k := 658) (ds := 8) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_0_3 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_0_3 _ _ _ _ _ hacc _
  · -- size 1, opc 0
    refine reg_case (k := 664) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_reg_1_0 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_1_0 _ _ _ _ _ hacc _
  · -- size 1, opc 1
    refine reg_case (k := 657) (ds := 16) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_1_1 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_1_1 _ _ _ _ _ hacc _
  · -- size 1, opc 2
    refine reg_case (k := 659) (ds := 16) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_1_2 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_1_2 _ _ _ _ _ hacc _
  · -- size 1, opc 3
    refine reg_case (k := 659) (ds := 16) (rs := 32) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_1_3 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_1_3 _ _ _ _ _ hacc _
  · -- size 2, opc 0
    refine reg_case (k := 662) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_reg_2_0 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_2_0 _ _ _ _ _ hacc _
  · -- size 2, opc 1
    refine reg_case (k := 655) (ds := 32) (rs := 32) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_2_1 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_2_1 _ _ _ _ _ hacc _
  · -- size 2, opc 2
    refine reg_case (k := 660) (ds := 32) (rs := 64) (sgn := true) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_2_2 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_2_2 _ _ _ _ _ hacc _
  · exact absurd hv (by decide)
  · -- size 3, opc 0
    refine reg_case (k := 662) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_STORE) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inr ⟨rfl, rfl, by unfold StoreCase; decide⟩) hj
    rw [run_LS_reg_3_0 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_3_0 _ _ _ _ _ hacc _
  · -- size 3, opc 1
    refine reg_case (k := 655) (ds := 64) (rs := 64) (sgn := false) (mem := .MemOp_LOAD) hw h0 h1 h2 h21 h10 hopt h hm hc hU
      e1 e2 hv hnp (fun st hst => ?_) (Or.inl ⟨rfl, by unfold LoadCase; decide⟩) hj
    rw [run_LS_reg_3_1 hw h0 h1 h2 h21 h10 (by omega) (by omega) hst,
      show fld w 22 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 2 hw]; simp; omega),
      show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega)]
    exact run_dec_reg_3_1 _ _ _ _ _ hacc _
  · exact absurd ⟨rfl, rfl⟩ hnp
  · exact absurd hv (by decide)

end JanusASL.Proofs
