import JanusASL.Proofs.LdStOrd

/-! # Proved: LDAPR (RCpc), LDXR/LDAXR (exclusive loads; the monitor is not modelled by Janus) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

theorem run_CreateAccDescLDAcqPC {s : SState} (h : LinuxEL0Config s) (tc : Bool) :
    (CreateAccDescLDAcqPC tc).run s = .ok { acqPCAcc with tagchecked := tc } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  cfg_simp [CreateAccDescLDAcqPC, NewAccDesc, undefined_AccessDescriptor, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_GenMPAMcurEL h, HaveTME, run_IsFeatureImplemented h, run_readReg htm, htd, acqPCAcc, gprAcc, run_internal_pick,
    undefined_AccessType, undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope,
    undefined_CacheType, undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, EL0]

set_option maxHeartbeats 16000000 in
theorem run_exec_ldapr {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) (hrs : rs = if ds = 64 then 64 else 32) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (tc : Bool) (hj : Janus.Arm64.execOrdered js size true rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_ordered_rcpc ds rn 0 rs rt tc false false).run s = .ok () s' ∧
      Rel js2 s' ∧ MemRel js2.mem s' ∧ RStep s s' := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execOrdered_load hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat false := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  obtain ⟨v, hv, hvn⟩ := run_Mem_read_al hc hm accGood_acqPC base (Int.ediv (ds : Int) 8).toNat
    (by rw [hdsn]; exact hsz) (by rw [hdsn]; exact hacc) (by rw [hdsn]; exact hal)
    (fun al => hU.trans_ord s hf base false al _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩)) hr0) (hU.nodev _ hr0) tc
  have hcr := run_CreateAccDescLDAcqPC hc tc
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
  unfold execute_aarch64_instrs_memory_ordered_rcpc
  cfg_simp [run_readReg hp, he, EL0, hcr, hB, hv, has, has3, undefined_AccessDescriptor, undefined_AccessType,
    undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope, undefined_CacheType,
    undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, run_internal_pick, hx1,
    run_readReg hc1.speInFlight]

theorem run_CreateAccDescExLDST {s : SState} (h : LinuxEL0Config s) (ar tc : Bool) :
    (CreateAccDescExLDST .MemOp_LOAD ar tc).run s = .ok { exclAcc false ar with tagchecked := tc } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  cases ar <;>
  cfg_simp [CreateAccDescExLDST, NewAccDesc, undefined_AccessDescriptor, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_GenMPAMcurEL h, HaveTME, run_IsFeatureImplemented h, run_readReg htm, htd, exclAcc, gprAcc, run_internal_pick,
    undefined_AccessType, undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope,
    undefined_CacheType, undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, EL0]

/-- The local exclusive monitor's state after a load-exclusive of `n` bytes at `va`
(janus_splice.sail: `MarkExclusiveLocal`; the address is the identity translation). -/
def monSet (s : SState) (va : BitVec 64) (n : Int) : SState :=
  (((s.set .__ExclusiveMonitorSet true).set .__janus_excl_valid true).set .__janus_excl_addr (va.setWidth 56)).set
    .__janus_excl_size n

/-- The registers a load-exclusive writes besides the destination. -/
def monRegs : List Register := [.__ExclusiveMonitorSet, .__janus_excl_valid, .__janus_excl_addr, .__janus_excl_size]

theorem monSet_get (s : SState) (va : BitVec 64) (n : Int) (r : Register) (hr : r ∉ monRegs) :
    (monSet s va n).regs.get? r = s.regs.get? r := by
  have h1 : r ≠ .__ExclusiveMonitorSet := fun e => hr (e ▸ by decide)
  have h2 : r ≠ .__janus_excl_valid := fun e => hr (e ▸ by decide)
  have h3 : r ≠ .__janus_excl_addr := fun e => hr (e ▸ by decide)
  have h4 : r ≠ .__janus_excl_size := fun e => hr (e ▸ by decide)
  simp only [monSet]
  rw [get?_set_ne _ _ (Ne.symm h4), get?_set_ne _ _ (Ne.symm h3), get?_set_ne _ _ (Ne.symm h2),
    get?_set_ne _ _ (Ne.symm h1)]

theorem cfg_not_mon : ∀ r ∈ cfgRegs, r ∉ monRegs := by decide

theorem mon_entry (r : Register) (h : r ∉ stepEntryRegs) : r ∉ monRegs := fun hm =>
  h (by simp only [monRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> decide)

theorem monSet_cfg {s : SState} (hc : LinuxEL0Config s) (va : BitVec 64) (n : Int) : LinuxEL0Config (monSet s va n) :=
  hc.of_eq fun r hr => monSet_get s va n r (cfg_not_mon r hr)

theorem monSet_rel {js : Janus.Arm64.State} {s : SState} (h : Rel js s) (va : BitVec 64) (n : Int) :
    Rel js (monSet s va n) :=
  (((h.set_other _ _ rfl (by decide) (by decide) (by decide)).set_other _ _ rfl (by decide) (by decide)
    (by decide)).set_other _ _ rfl (by decide) (by decide) (by decide)).set_other _ _ rfl (by decide) (by decide)
    (by decide)

theorem run_SetExclusiveMonitors {s : SState} (hc : LinuxEL0Config s) (va : BitVec 64) (n : Int) (hn : 0 < n)
    (hal : va.toNat % n.toNat = 0)
    (hT : ∃ d, (AArch64_TranslateAddress va (exclAcc false false) true n).run
      (s.set .__ExclusiveMonitorSet true) = .ok d (s.set .__ExclusiveMonitorSet true) ∧ TransOK d va) :
    (AArch64_SetExclusiveMonitors va n).run s = .ok () (monSet s va n) := by
  obtain ⟨d, hd, hok⟩ := hT
  have hc1 : LinuxEL0Config (s.set .__ExclusiveMonitorSet true) :=
    hc.of_eq fun r hr => get?_set_ne _ _ (fun e => by subst e; revert hr; decide)
  have hal' : IsAligned__1 va n = true := by
    rw [show n = ((n.toNat : Nat) : Int) by omega, isAligned_iff va n.toNat (by omega)]; simp [hal]
  have hcr := run_CreateAccDescExLDST hc1 false false
  unfold AArch64_SetExclusiveMonitors
  cfg_simp [hcr, hal', show ({ exclAcc false false with tagchecked := false } : AccessDescriptor) = exclAcc false false
    from rfl, hd, IsFault, hok.fault, MarkExclusiveLocal, MarkExclusiveGlobal, AArch64_MarkExclusiveVA, ProcessorID,
    hok.pa, monSet]

def GFrameX (s s' : SState) : Prop :=
  ∀ r, isGprReg r = false → r ≠ .SP_EL0 → r ∉ monRegs → s'.regs.get? r = s.regs.get? r

set_option maxHeartbeats 16000000 in
theorem run_exec_ldx {js js1 : Janus.Arm64.State} {s0 s : SState} (h : Rel js s) (hm : MemRel js.mem s)
    (hc : LinuxEL0Config s) (hU : UserMapped js.mem s0) (hf : TFrame js.mem s0 s) {size ds rs : Nat}
    (hcase : StoreCase size ds) (hrs : rs = if ds = 64 then 64 else 32) {rn rt : Nat} (hn : rn < 32) (ht : rt < 32)
    (ar tc : Bool) (rs' rt2 : Nat) (hj : Janus.Arm64.execOrdered js size true rn rt = .ok js1) :
    ∃ js2 s', js1 = js2.next ∧ js2.pc = js.pc ∧
      (execute_aarch64_instrs_memory_exclusive_single ar ds ds .MemOp_LOAD rn false rs false false rs' rt rt2 tc).run s =
        .ok () s' ∧ Rel js2 s' ∧ MemRel js2.mem s' ∧ GFrameX s s' := by
  obtain ⟨hds, hdsn, hsz, hds8⟩ := hcase.facts
  obtain ⟨p, hp, he, _, hsp⟩ := hc.pstate
  obtain ⟨base, hb, hal, hacc, rfl⟩ := execOrdered_load hj
  have hB := run_base h hc hn hb
  have hreg := accessible_bytes hacc
  have hr0 : InRegion js.mem base.toNat false := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  -- the monitor write
  let s1 := monSet s base (Int.ediv (ds : Int) 8)
  have hf1 : TFrame js.mem s0 s1 :=
    ⟨fun r h1 h2 h3 => by
      rw [monSet_get _ _ _ r (mon_entry r h3)]
      exact hf.regs r h1 h2 h3, hf.mem, hf.cycle, hf.out⟩
  have hc1 : LinuxEL0Config s1 := monSet_cfg hc _ _
  have hm1 : MemRel js.mem s1 := hm
  have h1 : Rel js s1 := monSet_rel h _ _
  have hB1 := run_base h1 hc1 hn hb
  have hf0 : TFrame js.mem s0 (s.set .__ExclusiveMonitorSet true) :=
    ⟨fun r h1 h2 h3 => by rw [get?_set_ne _ _ (fun e => by subst e; exact h3 (by decide))]; exact hf.regs r h1 h2 h3,
      hf.mem, hf.cycle, hf.out⟩
  have hSM := run_SetExclusiveMonitors hc base (Int.ediv (ds : Int) 8) (by have := hsz; omega)
    (by rw [hdsn]; exact hal)
    (hU.trans_ord _ hf0 base false true _ _ (Or.inr (Or.inr (Or.inl ⟨false, rfl⟩))) hr0)
  obtain ⟨v, hv, hvn⟩ := run_Mem_read_al hc1 hm1 (accGood_excl false ar) base (Int.ediv (ds : Int) 8).toNat
    (by rw [hdsn]; exact hsz) (by rw [hdsn]; exact hacc) (by rw [hdsn]; exact hal)
    (fun al => hU.trans_ord s1 hf1 base false al _ _ (Or.inr (Or.inr (Or.inl ⟨ar, rfl⟩))) hr0) (hU.nodev _ hr0) tc
  have hcr := run_CreateAccDescExLDST hc ar tc
  have has : (decide (0 ≤ ds) && decide (ds ≤ rs)) = true := by subst hrs; simp; split <;> omega
  have has3 : decide (ds ≤ rs) = true := by subst hrs; simp; split <;> omega
  have hrs' : rs = 32 ∨ rs = 64 := by subst hrs; split <;> simp
  obtain ⟨s2, hx2, hr2, hst2⟩ := run_X_set_r h1 ht hrs' (Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs)
  have hval : (Sail.BitVec.zeroExtend (BitVec.setWidth ds v) rs).setWidth 64 =
      BitVec.ofNat 64 (js.mem.readLE base.toNat (2 ^ size)) := by
    have hl := load_value (size := size) (opc := 1) (ds := ds) (rs := rs) (sgn := false)
      (by unfold StoreCase at hcase; unfold LoadCase; subst hrs
          rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hdsn v _ (by rw [hvn, hdsn])
    simpa [loadVal] using hl
  simp only [Janus.Arm64.State.setX, hval] at hr2
  have hc2 := hc1.rstep hst2
  refine ⟨_, s2, rfl, writeZR_pc _ _ _, ?_, hr2, by rw [writeZR_mem]; exact hm1.rstep hst2, fun r g1 g2 g3 => ?_⟩
  · unfold execute_aarch64_instrs_memory_exclusive_single
    simp only [s1] at hv hx2
    cfg_simp [run_readReg hp, he, EL0, hcr, hB, hSM, hB1, hv, has, has3, hx2, run_readReg hc2.speInFlight]
  · rw [hst2.regs r g1 g2]; exact monSet_get s base _ r g3

theorem step_agree_memX {w : Nat} {js js1 : Janus.Arm64.State} {s : SState} (h : Rel js s) (hc : LinuxEL0Config s)
    {k : Int} {s2 : SState}
    (hrun : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) = .ok () s2)
    (hr : Rel js1 s2) (hg : GFrameX (entrySt s w k) s2) (hpc : js1.pc = js.pc) :
    (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK (s2.set ._PC (js.pc + 4)) ∧
      Rel js1.next (s2.set ._PC (js.pc + 4)) ∧ LinuxEL0Config (s2.set ._PC (js.pc + 4)) := by
  have hbt : s2.regs.get? .__BranchTaken = some false := by
    rw [hg _ rfl (by decide) (by decide)]
    simp only [entrySt, stepEntry]; repeat rw [get?_set_ne _ _ (by decide)]
    exact get?_set_BranchTaken _ _
  have hpc2 : s2.regs.get? ._PC = some js.pc := by rw [hr.pc, hpc]
  refine ⟨run_janus_step (BitVec.ofNat 32 w) h.pc hrun hbt hpc2, by
    rw [show js1.next = { js1 with pc := js.pc + 4 } by simp [Janus.Arm64.State.next, hpc]]; exact hr.setPC _, ?_⟩
  refine hc.of_eq fun r hr => ?_
  rw [get?_set_ne _ _ (fun e => by subst e; revert hr; decide), hg r (cfgRegs_not_gpr r hr)
    (fun e => by subst e; revert hr; decide) (cfg_not_mon r hr),
    entry_get s w k r (cfg_not_entry r hr)]

theorem run_dec_ldx_0_0 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 0#1 Rs 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single false 8 8 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldxrb_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_0_1 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 0#1 Rs 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single false 16 16 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldxrh_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_0_2 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 0#1 Rs 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single false 32 32 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldxr_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_0_3 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 0#1 Rs 1#1 3#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single false 64 64 .MemOp_LOAD Rn.toNat false 64 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldxr_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_1_0 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldaxrb_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 1#1 Rs 1#1 0#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single true 8 8 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaxrb_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_1_1 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldaxrh_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 1#1 Rs 1#1 1#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single true 16 16 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaxrh_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_1_2 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 1#1 Rs 1#1 2#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single true 32 32 .MemOp_LOAD Rn.toNat false 32 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaxr_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldx_1_3 (Rt Rn Rt2 Rs : BitVec 5) (st : SState) :
    (decode_ldaxr_aarch64_instrs_memory_exclusive_single Rt Rn Rt2 1#1 Rs 1#1 3#2).run st =
      (execute_aarch64_instrs_memory_exclusive_single true 64 64 .MemOp_LOAD Rn.toNat false 64 false false
        Rs.toNat Rt.toNat Rt2.toNat (Rn.toNat != 31)).run st := by
  unfold decode_ldaxr_aarch64_instrs_memory_exclusive_single
  cfg_simp [undefined_Constraint, run_internal_pick]
  all_goals rfl

theorem run_dec_ldapr_0 (Rt Rn Rs : BitVec 5) (st : SState) :
    (decode_ldaprb_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs 0#2).run st =
      (execute_aarch64_instrs_memory_ordered_rcpc 8 Rn.toNat 0 32 Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldaprb_aarch64_instrs_memory_ordered_rcpc
  rfl

theorem run_dec_ldapr_1 (Rt Rn Rs : BitVec 5) (st : SState) :
    (decode_ldaprh_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs 1#2).run st =
      (execute_aarch64_instrs_memory_ordered_rcpc 16 Rn.toNat 0 32 Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldaprh_aarch64_instrs_memory_ordered_rcpc
  rfl

theorem run_dec_ldapr_2 (Rt Rn Rs : BitVec 5) (st : SState) :
    (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs 2#2).run st =
      (execute_aarch64_instrs_memory_ordered_rcpc 32 Rn.toNat 0 32 Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldapr_aarch64_instrs_memory_ordered_rcpc
  rfl

theorem run_dec_ldapr_3 (Rt Rn Rs : BitVec 5) (st : SState) :
    (decode_ldapr_aarch64_instrs_memory_ordered_rcpc Rt Rn Rs 3#2).run st =
      (execute_aarch64_instrs_memory_ordered_rcpc 64 Rn.toNat 0 64 Rt.toNat (Rn.toNat != 31) false false).run st := by
  unfold decode_ldapr_aarch64_instrs_memory_ordered_rcpc
  rfl

open Janus.Arm64 in
theorem decode_ldExcl {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 64 = 8) (h23 : (w / 2 ^ 23) % 2 = 0)
    (h22 : (w / 2 ^ 22) % 2 = 1) (h21 : (w / 2 ^ 21) % 2 = 0) (h16 : (w / 2 ^ 16) % 32 = 31)
    (h10 : (w / 2 ^ 10) % 32 = 31) :
    decode w = some (.ldExcl (bits w 31 30) (bit w 15) (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 4 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 1 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bits w 14 10 = 31 := by simp only [bits_def]; omega
  have e7 : bit w 23 = false := by simp only [bit_def]; simp; omega
  have e8 : bit w 21 = false := by simp only [bit_def]; simp; omega
  have e9 : bit w 22 = true := by simp only [bit_def]; simp; omega
  have e10 : bits w 20 16 = 31 := by simp only [bits_def]; omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, Bool.false_eq_true, ite_false, ite_true,
    decodeExclusive, e6, e7, e8, e9, e10, Bool.and_false, Bool.and_true, Bool.not_true, Bool.false_or, ne_eq,
    not_true_eq_false]
  simp

set_option maxHeartbeats 16000000 in
/-- **LDXR/LDAXR (and the B/H forms)**: for every word `size 001000 0 1 0 11111 o0 11111 Rn Rt` and every
related pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the word (an
aligned load; Janus does not model the exclusive monitor, which the ASL sets) the generated ASL
step completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldExcl_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 24) % 64 = 8) (h23 : (w / 2 ^ 23) % 2 = 0)
    (h22 : (w / 2 ^ 22) % 2 = 1) (h21 : (w / 2 ^ 21) % 2 = 0) (h16 : (w / 2 ^ 16) % 32 = 31)
    (h10 : (w / 2 ^ 10) % 32 = 31)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_ldExcl hw h0 h23 h22 h21 h16 h10)] at hj
  simp only [Janus.Arm64.exec] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 15) % 2 = 0 ∨ (w / 2 ^ 15) % 2 = 1 by omega) with ho | ho <;>
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- o0 0, size 0
    have hF := entry_facts h hm hc w 587
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 0 8 by unfold StoreCase; decide) (by decide) hn32 ht32 false _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single false 8 8 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 587) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_0_0 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_0_0, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 587) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 0, size 1
    have hF := entry_facts h hm hc w 588
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 1 16 by unfold StoreCase; decide) (by decide) hn32 ht32 false _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single false 16 16 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 588) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_0_1 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_0_1, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 588) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 0, size 2
    have hF := entry_facts h hm hc w 586
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 2 32 by unfold StoreCase; decide) (by decide) hn32 ht32 false _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single false 32 32 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 586) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_0_2 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_0_2, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 586) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 0, size 3
    have hF := entry_facts h hm hc w 586
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 64) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 3 64 by unfold StoreCase; decide) (by decide) hn32 ht32 false _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single false 64 64 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          64 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 586) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_0_3 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 0#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_0_3, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 586) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 1, size 0
    have hF := entry_facts h hm hc w 584
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 0 8 by unfold StoreCase; decide) (by decide) hn32 ht32 true _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single true 8 8 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 584) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_1_0 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_1_0, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 584) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 1, size 1
    have hF := entry_facts h hm hc w 585
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 1 16 by unfold StoreCase; decide) (by decide) hn32 ht32 true _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single true 16 16 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 585) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_1_1 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_1_1, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 585) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 1, size 2
    have hF := entry_facts h hm hc w 583
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 2 32 by unfold StoreCase; decide) (by decide) hn32 ht32 true _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single true 32 32 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          32 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 583) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_1_2 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_1_2, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 583) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- o0 1, size 3
    have hF := entry_facts h hm hc w 583
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldx (rs := 64) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 3 64 by unfold StoreCase; decide) (by decide) hn32 ht32 true _
      (fld w 16 5).toNat (fld w 10 5).toNat hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_exclusive_single true 64 64 .MemOp_LOAD (Janus.Arm64.bits w 9 5) false
          64 false false (fld w 16 5).toNat (Janus.Arm64.bits w 4 0) (fld w 10 5).toNat ((fld w 5 5).toNat != 31)).run
          (entrySt s w 583) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldx_1_3 hw h0 h23 h22 h21 (by omega) h16 h10 (by omega)
        (see_entry s _),
        show fld w 15 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 15 1 hw]; simp; omega),
        show fld w 22 1 = 1#1 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 22 1 hw]; simp; omega),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldx_1_3, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_memX h hc (k := 583) (hdec.trans hr2) hrel hst hpc
    exact ⟨_, e1, e2, hmem, e3⟩

open Janus.Arm64 in
theorem decode_ldapr {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h23 : (w / 2 ^ 23) % 2 = 1) (h22 : (w / 2 ^ 22) % 2 = 0) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h16 : (w / 2 ^ 16) % 32 = 31) (h15 : (w / 2 ^ 15) % 2 = 1) (h12 : (w / 2 ^ 12) % 8 = 4)
    (h10 : (w / 2 ^ 10) % 4 = 0) :
    decode w = some (.ldstOrdered (bits w 31 30) true true (bits w 9 5) (bits w 4 0)) := by
  have e1 : ¬ w ≥ 2 ^ 32 := by omega
  have e2 : bits w 28 25 = 12 := by simp only [bits_def]; omega
  have e3 : bit w 26 = false := by simp only [bit_def]; simp; omega
  have e4 : bits w 29 27 = 7 := by simp only [bits_def]; omega
  have e5 : bit w 24 = false := by simp only [bit_def]; simp; omega
  have e6 : bit w 21 = true := by simp only [bit_def]; simp; omega
  have e7 : bits w 11 10 = 0 := by simp only [bits_def]; omega
  have e8 : bit w 15 = true := by simp only [bit_def]; simp; omega
  have e9 : bits w 14 12 = 4 := by simp only [bits_def]; omega
  have e10 : bit w 23 = true := by simp only [bit_def]; simp; omega
  have e11 : bit w 22 = false := by simp only [bit_def]; simp; omega
  have e12 : bits w 20 16 = 31 := by simp only [bits_def]; omega
  have e14 : bits w 11 10 ≠ 2 := by omega
  simp only [decode, e1, e2, if_false, decodeLdSt, e3, e4, e5, e6, e7, e14, Bool.false_eq_true, ite_false, ite_true,
    Bool.not_false, Bool.not_true, decodeAtomic, e8, e9, e10, e11, e12]
  simp

set_option maxHeartbeats 16000000 in
/-- **LDAPR (and LDAPRB/H)**: for every word `size 111 0 00 1 0 1 11111 1 100 00 Rn Rt` and every related
pair of states under `LinuxEL0Config` and `UserMapped`, whenever Janus steps the word the generated
ASL step completes in a related state, with Janus' memory related to the ASL's. -/
theorem ldapr_agree {w : Nat} (hw : w < 2 ^ 32) (h0 : (w / 2 ^ 27) % 8 = 7) (h1 : (w / 2 ^ 26) % 2 = 0)
    (h2 : (w / 2 ^ 24) % 4 = 0) (h23 : (w / 2 ^ 23) % 2 = 1) (h22 : (w / 2 ^ 22) % 2 = 0) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h16 : (w / 2 ^ 16) % 32 = 31) (h15 : (w / 2 ^ 15) % 2 = 1) (h12 : (w / 2 ^ 12) % 8 = 4)
    (h10 : (w / 2 ^ 10) % 4 = 0)
    {js js' : Janus.Arm64.State} {s : SState} (h : Rel js s) (hm : MemRel js.mem s) (hc : LinuxEL0Config s)
    (hU : UserMapped js.mem s) (hj : Janus.Arm64.step w js = .ok js') :
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ MemRel js'.mem s' ∧
      LinuxEL0Config s' := by
  rw [Janus.Arm64.step_of_decode (decode_ldapr hw h0 h1 h2 h23 h22 h21 h16 h15 h12 h10)] at hj
  simp only [Janus.Arm64.exec] at hj
  have hrn : (fld w 5 5).toNat = Janus.Arm64.bits w 9 5 := (bits_eq_fld w 9 5 hw).symm
  have hrt : (fld w 0 5).toNat = Janus.Arm64.bits w 4 0 := (bits_eq_fld w 4 0 hw).symm
  have hn32 : Janus.Arm64.bits w 9 5 < 32 := by simp only [bits_def]; omega
  have ht32 : Janus.Arm64.bits w 4 0 < 32 := by simp only [bits_def]; omega
  have hb3130 : Janus.Arm64.bits w 31 30 = (w / 2 ^ 30) % 4 := by simp only [bits_def]
  rw [hb3130] at hj
  rcases (show (w / 2 ^ 30) % 4 = 0 ∨ (w / 2 ^ 30) % 4 = 1 ∨ (w / 2 ^ 30) % 4 = 2 ∨ (w / 2 ^ 30) % 4 = 3 by omega)
    with e | e | e | e <;> rw [e] at hj
  · -- size 0
    have hF := entry_facts h hm hc w 553
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldapr (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 0 8 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered_rcpc 8 (Janus.Arm64.bits w 9 5) 0 32 (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w 553) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldapr_0 hw h0 h1 h2 h23 h22 h21 h16 h15 h12 h10 (by omega)
        (see_entry s _),
        show fld w 30 2 = 0#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldapr_0, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 553) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- size 1
    have hF := entry_facts h hm hc w 554
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldapr (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 1 16 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered_rcpc 16 (Janus.Arm64.bits w 9 5) 0 32 (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w 554) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldapr_1 hw h0 h1 h2 h23 h22 h21 h16 h15 h12 h10 (by omega)
        (see_entry s _),
        show fld w 30 2 = 1#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldapr_1, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 554) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- size 2
    have hF := entry_facts h hm hc w 551
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldapr (rs := 32) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 2 32 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered_rcpc 32 (Janus.Arm64.bits w 9 5) 0 32 (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w 551) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldapr_2 hw h0 h1 h2 h23 h22 h21 h16 h15 h12 h10 (by omega)
        (see_entry s _),
        show fld w 30 2 = 2#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldapr_2, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 551) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩
  · -- size 3
    have hF := entry_facts h hm hc w 551
    obtain ⟨js2, s2, rfl, hpc, hr2, hrel, hmem, hst⟩ := run_exec_ldapr (rs := 64) hF.1 hF.2.1 hF.2.2.1 hU hF.2.2.2
      (show StoreCase 3 64 by unfold StoreCase; decide) (by decide) hn32 ht32 _ hj
    have hdec : (__DecodeA64 (js.pc.toNat : Int) (BitVec.ofNat 32 w)).run (stepEntry s (BitVec.ofNat 32 w)) =
        (execute_aarch64_instrs_memory_ordered_rcpc 64 (Janus.Arm64.bits w 9 5) 0 64 (Janus.Arm64.bits w 4 0)
          ((fld w 5 5).toNat != 31) false false).run (entrySt s w 551) := by
      rw [run_DecodeA64_LS' hw (by omega) (by omega), run_LS_ldapr_3 hw h0 h1 h2 h23 h22 h21 h16 h15 h12 h10 (by omega)
        (see_entry s _),
        show fld w 30 2 = 3#2 from BitVec.eq_of_toNat_eq (by rw [fld_toNat w 30 2 hw]; simp; omega),
        run_dec_ldapr_3, hrn, hrt]
    obtain ⟨e1, e2, e3⟩ := step_agree_mem h hc (k := 551) (hdec.trans hr2) hrel hst.regs hpc
    exact ⟨_, e1, e2, hmem, e3⟩

end JanusASL.Proofs
