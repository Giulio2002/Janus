import JanusASL.Proofs.LdStPair
import JanusASL.Proofs.MemOrd

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

end JanusASL.Proofs
