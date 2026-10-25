import JanusASL.Proofs.LdStPair
import JanusASL.Proofs.MemOrd
import JanusASL.Proofs.LdStDecodeO

/-! # Proved: LDAR/STLR (and LDARB/H, STLRB/H) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_CreateAccDescAcqRel {s : SState} (h : LinuxEL0Config s) (w tc : Bool) :
    (CreateAccDescAcqRel (if w then .MemOp_STORE else .MemOp_LOAD) tc).run s =
      .ok { acqRelAcc w with tagchecked := tc } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  cases w <;>
  cfg_simp [CreateAccDescAcqRel, NewAccDesc, undefined_AccessDescriptor, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_GenMPAMcurEL h, HaveTME, run_IsFeatureImplemented h, run_readReg htm, htd, acqRelAcc, gprAcc, run_internal_pick,
    undefined_AccessType, undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope,
    undefined_CacheType, undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, EL0]

theorem execOrdered_load {js js1 : Janus.Arm64.State} {size rn rt : Nat}
    (h : Janus.Arm64.execOrdered js size true rn rt = .ok js1) :
    ∃ base, Janus.Arm64.baseAddr js rn = .ok base ∧ base.toNat % 2 ^ size = 0 ∧
      js.mem.accessible base.toNat (2 ^ size) false = true ∧
      js1 = (js.writeZR rt (BitVec.ofNat 64 (js.mem.readLE base.toNat (2 ^ size)))).next := by
  unfold Janus.Arm64.execOrdered at h
  split at h
  · cases h
  · next base hb =>
    simp only at h
    split at h
    · cases h
    · next hal =>
      simp only [ite_true] at h
      split at h
      · cases h
      · next v hl =>
        obtain ⟨ha, rfl⟩ := load_ok hl
        cases h
        exact ⟨base, hb, by omega, ha, rfl⟩

theorem execOrdered_store {js js1 : Janus.Arm64.State} {size rn rt : Nat}
    (h : Janus.Arm64.execOrdered js size false rn rt = .ok js1) :
    ∃ base, Janus.Arm64.baseAddr js rn = .ok base ∧ base.toNat % 2 ^ size = 0 ∧
      js.mem.accessible base.toNat (2 ^ size) true = true ∧
      js1 = { js with mem := js.mem.writeLE base.toNat (2 ^ size) (js.readZR rt).toNat }.next := by
  unfold Janus.Arm64.execOrdered at h
  split at h
  · cases h
  · next base hb =>
    simp only at h
    split at h
    · cases h
    · next hal =>
      simp only [Bool.false_eq_true, ite_false] at h
      split at h
      · cases h
      · next m hs =>
        obtain ⟨ha, rfl⟩ := store_ok hs
        cases h
        exact ⟨base, hb, by omega, ha, rfl⟩

set_option maxHeartbeats 16000000 in
theorem run_exec_ord_load {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) (hrs : rs = if ds = 64 then 64 else 32) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (tc : Bool) (hj : Janus.Arm64.execOrdered js size true rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_ordered ds false .MemOp_LOAD rn 0 rs false rt tc false).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ RStep s s' := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execOrdered_load hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat false := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  obtain ⟨v, hv, hvn⟩ := run_Mem_read_al hc hm (accGood_acqRel false) base (Int.ediv (ds : Int) 8).toNat
    (by rw [hdsn]; exact hsz) (by rw [hdsn]; exact hacc) (by rw [hdsn]; exact hal)
    (fun al => hU.trans_ord s hf base false al _ _ (Or.inl rfl) hr0) (hU.nodev _ hr0) tc
  have hcr := run_CreateAccDescAcqRel hc false tc
  simp only [Bool.false_eq_true, ite_false] at hcr
  have has : (decide (0 ≤ ds) && decide (ds ≤ rs)) = true := by subst hrs; simp; split <;> omega
  have has3 : decide (ds ≤ rs) = true := by subst hrs; simp; split <;> omega
  have hrs' : rs = 32 ∨ rs = 64 := by subst hrs; split <;> simp
  obtain ⟨s1, hx1, hr1, hst1⟩ := run_X_set_r h ht hrs' (Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs)
  have hval : (Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat (2 ^ size)) := by
    have hl := load_value (size := size) (opc := 1) (ds := ds) (rs := rs) (sgn := false)
      (by unfold StoreCase at hcase; unfold LoadCase; subst hrs
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hdsn v _ (by rw [hvn, hdsn])
    simpa [loadVal] using hl
  simp only [Janus.Arm64.State.setX, hval] at hr1
  have hc1 := hc.rstep hst1
  refine ⟨_, s1, rfl, writeZR_pc _ _ _, ?_, hr1, by rw [writeZR_mem]; exact hm.rstep hst1, hst1⟩
  unfold execute_aarch64_instrs_memory_ordered
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hv, has, has3, undefined_AccessDescriptor, undefined_AccessType,
    undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope, undefined_CacheType,
    undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, run_internal_pick, hx1,
    run_readReg hc1.speInFlight]

set_option maxHeartbeats 16000000 in
theorem run_exec_ord_store {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (tc : Bool) (hj : Janus.Arm64.execOrdered js size false rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_ordered ds false .MemOp_STORE rn 0 rs false rt tc false).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrame s s' := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execOrdered_store hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat true := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have ea0 : Sail.BitVec.addInt base 0 = base := by apply BitVec.eq_of_toNat_eq; simp [Sail.BitVec.addInt]
  have hX := run_X_read_w h ht hds
  obtain ⟨s1, hv, hst⟩ := run_Mem_set_al hc (accGood_acqRel true) base (Int.ediv (ds : Int) 8).toNat
    (by rw [hdsn]; exact hsz) (by rw [hdsn]; exact hacc) (by rw [hdsn]; exact hal)
    (fun al => hU.trans_ord s hf base true al _ _ (Or.inl rfl) hr0) (hU.nodev _ hr0.read) tc
    (BitVec.setWidth _ (BitVec.setWidth ds (js.readZR rt)))
  have hcr := run_CreateAccDescAcqRel hc true tc
  simp only [ite_true] at hcr
  have hr1 := h.mem_update hst.regs (js.mem.writeLE base.toNat (2 ^ size) (js.readZR rt).toNat)
  have hm1 : MemRel (js.mem.writeLE base.toNat (2 ^ size) (js.readZR rt).toNat) s1 := by
    refine hm.store (hdsn ▸ hst) ?_
    simp only [BitVec.toNat_setWidth, hdsn]
    rw [show 2 ^ size * 8 = 8 * 2 ^ size by omega, ← hds8, Nat.mod_mod, Nat.mod_mod]
  have hc1 : LinuxEL0Config s1 := hc.stored hst
  refine ⟨_, s1, rfl, rfl, ?_, hr1, hm1, fun r _ _ => by show s1.regs.get? r = s.regs.get? r; rw [hst.regs]⟩
  unfold execute_aarch64_instrs_memory_ordered
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hv, ea0, hX, undefined_AccessDescriptor, undefined_AccessType,
    undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope, undefined_CacheType,
    undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, run_internal_pick,
    run_readReg hc1.speInFlight]

theorem run_dec_ord_0_0 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_stlrb_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 0#1 0#2).run st =
      (execute_aarch64_instrs_memory_ordered 8 false .MemOp_STORE Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_stlrb_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_0_1 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_stlrh_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 0#1 1#2).run st =
      (execute_aarch64_instrs_memory_ordered 16 false .MemOp_STORE Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_stlrh_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_0_2 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 0#1 2#2).run st =
      (execute_aarch64_instrs_memory_ordered 32 false .MemOp_STORE Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_stlr_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_0_3 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_stlr_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 0#1 3#2).run st =
      (execute_aarch64_instrs_memory_ordered 64 false .MemOp_STORE Rn.toNat 0 64 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_stlr_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_1_0 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldarb_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_ordered 8 false .MemOp_LOAD Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_ldarb_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_1_1 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldarh_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_ordered 16 false .MemOp_LOAD Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_ldarh_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_1_2 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_ordered 32 false .MemOp_LOAD Rn.toNat 0 32 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_ldar_aarch64_instrs_memory_ordered
  rfl

theorem run_dec_ord_1_3 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldar_aarch64_instrs_memory_ordered Rt Rn Rt2 1#1 Rs 1#1 3#2).run st =
      (execute_aarch64_instrs_memory_ordered 64 false .MemOp_LOAD Rn.toNat 0 64 false Rt.toNat (Rn.toNat != 31) false).run st := by
  unfold decode_ldar_aarch64_instrs_memory_ordered
  rfl

open Janus.Arm64 in
theorem decode_ldstOrdered {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 64 = 8) (h23 : (w / 2 ^ 23) % 2 = 1)
    (h21 : (w / 2 ^ 21) % 2 = 0) (h15 : (w / 2 ^ 15) % 2 = 1) (h16 : (w / 2 ^ 16) % 32 = 31)
    (h10 : (w / 2 ^ 10) % 32 = 31) :
    decode w = some (.ldstOrdered (bits w 31 30) (bit w 22) false (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 4 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 1 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bits w 14 10 = 31 := by simp only [bits_def]; omega
  have e7 : bit w 23 = true := by simp only [bit_def]; simp; omega
  have e8 : bit w 21 = false := by simp only [bit_def]; simp; omega
  have e9 : bit w 15 = true := by simp only [bit_def]; simp; omega
  have e10 : bits w 20 16 = 31 := by simp only [bits_def]; omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, Bool.false_eq_true, ite_false, ite_true,
    decodeExclusive, e6, e7, e8, e9, e10, Bool.and_false, Bool.and_true, Bool.not_true, Bool.false_or, ne_eq,
    not_true_eq_false]
  simp

set_option maxHeartbeats 16000000 in
/-- **LDAR/STLR (and the B/H forms)**: for every word `size 001000 1 L 0 11111 1 11111 Rn Rt` and
every related pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the word
(the address is naturally aligned) the generated ASL step completes in a related state, with
Janus' memory related to the ASL's. -/
theorem ldstOrdered_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 64 = 8) (h23 : (w / 2 ^ 23) % 2 = 1)
    (h21 : (w / 2 ^ 21) % 2 = 0) (h15 : (w / 2 ^ 15) % 2 = 1) (h16 : (w / 2 ^ 16) % 32 = 31)
    (h10 : (w / 2 ^ 10) % 32 = 31)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_ldstOrdered hw h0 h23 h21 h15 h16 h10)] at hj
  simp only [Janus.Arm64.exec] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  have hb22 : Janus.Arm64.bit w 22 = ((w / 2 ^ 22) % 2 == 1) := by simp only [bit_def]
  rw [hb3130, hb22] at hj
  have hfacts := fun k => entry_facts h hm hc w k
  rcases (show (w / 2 ^ 22) % 2 = 0 ∨ (w / 2 ^ 22) % 2 = 1 by omega) with hL | hL <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [hL, e] at hj <;>
  simp only [show (0 == 1) = false from rfl, show (1 == 1) = true from rfl] at hj
  · -- L 0, size 0
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_store (rs := 32) (hfacts 577).1 (hfacts 577).2.1 (hfacts 577).2.2.1 hU (hfacts 577).2.2.2
      (show StoreCase 0 8 by unfold StoreCase; decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 8 false .MemOp_STORE (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 577) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_0_0 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_0_0, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 577) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 0, size 1
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_store (rs := 32) (hfacts 578).1 (hfacts 578).2.1 (hfacts 578).2.2.1 hU (hfacts 578).2.2.2
      (show StoreCase 1 16 by unfold StoreCase; decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 16 false .MemOp_STORE (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 578) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_0_1 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_0_1, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 578) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 0, size 2
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_store (rs := 32) (hfacts 575).1 (hfacts 575).2.1 (hfacts 575).2.2.1 hU (hfacts 575).2.2.2
      (show StoreCase 2 32 by unfold StoreCase; decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 32 false .MemOp_STORE (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 575) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_0_2 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_0_2, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 575) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 0, size 3
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_store (rs := 64) (hfacts 575).1 (hfacts 575).2.1 (hfacts 575).2.2.1 hU (hfacts 575).2.2.2
      (show StoreCase 3 64 by unfold StoreCase; decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 64 false .MemOp_STORE (Janus.Arm64.bits w 9 5) 0 64
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 575) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_0_3 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_0_3, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 575) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 1, size 0
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_load (rs := 32) (hfacts 567).1 (hfacts 567).2.1 (hfacts 567).2.2.1 hU (hfacts 567).2.2.2
      (show StoreCase 0 8 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 8 false .MemOp_LOAD (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 567) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_1_0 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_1_0, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 567) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 1, size 1
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_load (rs := 32) (hfacts 568).1 (hfacts 568).2.1 (hfacts 568).2.2.1 hU (hfacts 568).2.2.2
      (show StoreCase 1 16 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 16 false .MemOp_LOAD (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 568) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_1_1 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_1_1, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 568) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 1, size 2
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_load (rs := 32) (hfacts 566).1 (hfacts 566).2.1 (hfacts 566).2.2.1 hU (hfacts 566).2.2.2
      (show StoreCase 2 32 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 32 false .MemOp_LOAD (Janus.Arm64.bits w 9 5) 0 32
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 566) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_1_2 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_1_2, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 566) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- L 1, size 3
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ord_load (rs := 64) (hfacts 566).1 (hfacts 566).2.1 (hfacts 566).2.2.1 hU (hfacts 566).2.2.2
      (show StoreCase 3 64 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered 64 false .MemOp_LOAD (Janus.Arm64.bits w 9 5) 0 64
          false (Janus.Arm64.bits w 4 0) ((fld w 5 5).toNat != 31) false).run (entrySt s w 566) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ord_1_3 hw h0 h23 (by omega) h21 h15 h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ord_1_3, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 566) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩

end JanusASL.Proofs
