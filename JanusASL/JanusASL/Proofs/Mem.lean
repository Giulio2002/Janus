import JanusASL.Proofs.Config
import JanusASL.Proofs.Rev

/-! # Loads and stores: memory through the ASL's translation (`UserMapped`) -/

set_option linter.unusedSimpArgs false

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

-- field getters of the registers the memory path reads
attribute [local simp] Mk_SCRType Sail.BitVec.extractLsb

theorem run_S1TranslationRegime' {s : SState} (h : LinuxEL0Config s) :
    (S1TranslationRegime 0#2).run s = .ok 1#2 s := run_S1TranslationRegime h

theorem run_AccessIsTagChecked {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) (acc : AccessDescriptor)
    (ht : acc.tagchecked = true) (hel : acc.el = 0#2) (hw : acc.write = false ∨ acc.write = true) :
    (AArch64_AccessIsTagChecked v acc).run s = .ok false s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  rcases access_cases v 55 with hb | hb <;>
  cfg_simp [AArch64_AccessIsTagChecked, ht, run_UsingAArch32 h, run_readReg hp, he, EffectiveMTX, EffectiveTBI,
    EffectiveTCMA, run_S1TranslationRegime h, run_ELUsingAArch32 h, HaveMTE4Ext, run_IsFeatureImplemented h, hb,
    run_readReg h.tcr1, HavePACExt, AArch64_AllocationTagAccessIsEnabled, run_readReg h.scr3, run_readReg h.hcr2,
    run_EL2Enabled h, EL0, EL1, EL2, EL3, _get_TCR_EL1_Type_MTX0, _get_TCR_EL1_Type_MTX1, _get_TCR_EL1_Type_TBI0,
    _get_TCR_EL1_Type_TBI1, _get_TCR_EL1_Type_TBID0, _get_TCR_EL1_Type_TBID1, _get_TCR_EL1_Type_TCMA0,
    _get_TCR_EL1_Type_TCMA1, _get_SCR_EL3_Type_ATA, _get_HCR_EL2_Type_ATA, _get_HCR_EL2_Type_E2H, _get_HCR_EL2_Type_TGE,
    hel, TranslationRegime, run_ELIsInHost h, run_readReg h.sctlr1, _get_SCTLR_EL1_Type_ATA0, HaveVirtHostExt]

open Sail.ConcurrencyInterfaceV1.PreSail in
theorem run_readByte {s : SState} {a : Nat} {b : BitVec 8} (h : s.mem.get? a = some b) :
    (readByte a : SailM (BitVec 8)).run s = .ok b s := by
  simp only [readByte, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h, pure,
    EStateM.pure]

theorem toNat_rec {a b : Nat} (h : a = b) (x : BitVec a) : (h ▸ x : BitVec b).toNat = x.toNat := by subst h; rfl

open Sail.ConcurrencyInterfaceV1.PreSail in
theorem run_readBytes {s : SState} (m : Janus.Arm64.Memory) :
    ∀ (n a : Nat), 0 < n → (∀ i < n, s.mem.get? (a + i) = some (m.bytes (a + i))) →
      ∃ v, (readBytes n a : SailM (BitVec (8 * n) × Option Bool)).run s = .ok (v, none) s ∧
        v.toNat = m.readLE a n := by
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ n ih =>
    intro a _ hm
    have h0 := hm 0 (by omega); simp only [Nat.add_zero] at h0
    cases n with
    | zero =>
      refine ⟨(m.bytes a : BitVec 8), ?_, ?_⟩
      · show (readBytes 1 a : SailM (BitVec 8 × Option Bool)).run s = _
        unfold readBytes
        simp only [run_bind, run_readByte h0, run_pure]
      · simp [Janus.Arm64.Memory.readLE]
    | succ n =>
      obtain ⟨v, hv, hvn⟩ := ih (a + 1) (by omega) (fun i hi => by
        have := hm (i + 1) (by omega); rw [show a + (i + 1) = a + 1 + i by omega] at this; exact this)
      refine ⟨(show 8 * (n + 1) + 8 = 8 * (n + 1 + 1) by omega) ▸ (v.append (m.bytes a)), ?_, ?_⟩
      · unfold readBytes
        simp only [run_bind, run_readByte h0, hv, run_pure]
      · refine (toNat_rec (a := 8 * (n + 1) + 8) (b := 8 * (n + 1 + 1)) (by omega) (v.append (m.bytes a))).trans ?_
        show (v ++ m.bytes a).toNat = _
        rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m.bytes a).isLt, Nat.shiftLeft_eq, hvn]
        simp only [Janus.Arm64.Memory.readLE]
        omega

/-- The access descriptor of an ordinary EL0 general-purpose load (`w = false`) or store
(`w = true`), as `CreateAccDescGPR` builds it under `LinuxEL0Config` (with `tagchecked` cleared, as
`AArch64_MemSingle_read`/`_set` leave it after `AArch64_AccessIsTagChecked`). -/
def gprAcc (w : Bool) : AccessDescriptor :=
  { acctype := .AccessType_GPR, el := 0#2, ss := .SS_NonSecure, acqsc := false, acqpc := false, relsc := false,
    limitedordered := false, exclusive := false, atomicop := false, modop := .MemAtomicOp_GCSSS1,
    nontemporal := false, read := !w, write := w, cacheop := .CacheOp_Clean, opscope := .CacheOpScope_SetWay,
    cachetype := .CacheType_Data, pan := true, transactional := false, nonfault := false, firstfault := false,
    first := false, contiguous := false, streamingsve := false, ls64 := false, mops := false, rcw := false,
    rcws := false, toplevel := false, varange := .VARange_LOWER, a32lsmd := false, tagchecked := false,
    tagaccess := false, mpam := { mpam_sp := .PIdSpace_NonSecure, partid := 0#16, pmg := 0#8 } }

theorem run_SecurityStateAtEL0 {s : SState} (h : LinuxEL0Config s) :
    (SecurityStateAtEL 0#2).run s = .ok .SS_NonSecure s := by
  unfold SecurityStateAtEL
  simp only [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run]
  cfg_simp [HaveRME, run_IsFeatureImplemented h, EL3, run_readReg h.scr3, _get_SCR_EL3_Type_NSE,
    EffectiveSCR_EL3_NS, run_EL2Enabled h, EL2, HaveSecureState, SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw, ExceptT.run_bind, liftM, ExceptT.run_lift,
    MonadExceptOf.throw, ExceptT.run_throw, monadLift, MonadLift.monadLift, _get_SCR_EL3_Type_NS,
    run_HaveSecureEL2Ext h, run_map, ExceptT.run_mk, ExceptT.run_pure]

theorem run_MPAMisEnabled {s : SState} (h : LinuxEL0Config s) : (MPAMisEnabled ()).run s = .ok false s := by
  cfg_simp [MPAMisEnabled, HighestEL, EL3, MPAM3_EL3_read, run_readReg h.mpam3, run_readReg h.mpam2,
    _get_MPAM3_EL3_Type_MPAMEN, Sail.BitVec.slice]

theorem pids_ns_beq : (PARTIDspaceType.PIdSpace_NonSecure == PARTIDspaceType.PIdSpace_NonSecure) = true := rfl

theorem run_GenMPAMcurEL {s : SState} (h : LinuxEL0Config s) (acctype : AccessType) :
    (GenMPAMcurEL acctype).run s = .ok { mpam_sp := .PIdSpace_NonSecure, partid := 0#16, pmg := 0#8 } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  unfold GenMPAMcurEL GenMPAMatEL
  simp only [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run]
  cfg_simp [run_readReg hp, he, run_SecurityStateAtEL0 h, PARTIDspaceFromSS, run_MPAMisEnabled h, DefaultMPAMinfo,
    undefined_MPAMinfo, undefined_PARTIDspaceType, run_internal_pick, DefaultPARTID, DefaultPMG, integer_subrange,
    ExceptT.run_bind, liftM, ExceptT.run_lift, monadLift, MonadLift.monadLift, ExceptT.run_mk, ExceptT.run_pure,
    pids_ns_beq, ExceptT.run_map, Sail.get_slice_int, Except.map, Bool.not_false]

theorem run_CreateAccDescGPR {s : SState} (h : LinuxEL0Config s) (w tc : Bool) :
    (CreateAccDescGPR (if w then .MemOp_STORE else .MemOp_LOAD) false false tc).run s =
      .ok { gprAcc w with tagchecked := tc } s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  cases w <;>
  cfg_simp [CreateAccDescGPR, NewAccDesc, undefined_AccessDescriptor, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_GenMPAMcurEL h, HaveTME, run_IsFeatureImplemented h, run_readReg htm, htd, gprAcc, run_internal_pick,
    undefined_AccessType, undefined_SecurityState, undefined_MemAtomicOp, undefined_CacheOp, undefined_CacheOpScope,
    undefined_CacheType, undefined_VARange, undefined_MPAMinfo, undefined_PARTIDspaceType, EL0]

/-! ## Alignment arithmetic -/

theorem align_bits_toNat (v : BitVec 64) (y : Nat) (hy : 0 < y) :
    (Align_bits v (y : Int)).toNat = v.toNat / y * y := by
  have h1 := v.isLt
  have h2 : v.toNat / y * y ≤ v.toNat := Nat.div_mul_le_self _ _
  have e : fdiv_int (Sail.BitVec.toNatInt v) (y : Int) * (y : Int) = ((v.toNat / y * y : Nat) : Int) := by
    have hm : ¬ ((y : Int) < 0) := by omega
    have hb : ((v.toNat : Int) < 0) = False := by simp
    simp [fdiv_int, hm, Sail.BitVec.toNatInt, Int.tdiv_eq_ediv_of_nonneg, hb]
  simp only [Align_bits, Slice_int, Align_int, Sail.get_slice_int, Sail.BitVec.length]
  rw [e]
  apply Nat.eq_of_beq_eq_true
  simp [BitVec.extractLsb', BitVec.toNat_ofInt]
  rw [show ((v.toNat : Int) / (y : Int) * (y : Int)) = ((v.toNat / y * y : Nat) : Int) by push_cast; rfl]
  omega

theorem isAligned_iff (v : BitVec 64) (y : Nat) (hy : 0 < y) : IsAligned__1 v (y : Int) = decide (v.toNat % y = 0) := by
  have := align_bits_toNat v y hy
  have h3 := Nat.mod_add_div v.toNat y
  simp only [IsAligned__1]
  by_cases h : v.toNat % y = 0
  · simp only [h, decide_true]
    apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq; rw [this]
    rw [Nat.mul_comm] at h3; omega
  · simp only [h, decide_false]
    apply beq_eq_false_iff_ne.mpr; intro e
    have := congrArg BitVec.toNat e; rw [align_bits_toNat v y hy] at this
    apply h; rw [Nat.mul_comm] at h3
    have : v.toNat % y = v.toNat - v.toNat / y * y := by omega
    rw [this]; omega

theorem run_AllInAlignedQuantity (s : SState) (v : BitVec 64) (n : Nat) (h1 : 1 ≤ n) (h16 : n ≤ 16)
    (hv : v.toNat + n ≤ 2 ^ 64) :
    (AllInAlignedQuantity v (n : Int) 16).run s = .ok (decide (v.toNat % 16 + n ≤ 16)) s := by
  have e : Sail.BitVec.subInt (Sail.BitVec.addInt v (n : Int)) 1 = BitVec.ofNat 64 (v.toNat + n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.subInt, Sail.BitVec.addInt]
    omega
  have hb : (Align_bits (BitVec.ofNat 64 (v.toNat + n - 1)) (16 : Nat) == Align_bits v (16 : Nat)) =
      decide (v.toNat % 16 + n ≤ 16) := by
    have a1 := align_bits_toNat (BitVec.ofNat 64 (v.toNat + n - 1)) 16 (by decide)
    have a2 := align_bits_toNat v 16 (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at a1
    by_cases hq : v.toNat % 16 + n ≤ 16
    · simp only [hq, decide_true]
      apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq; rw [a1, a2]; omega
    · simp only [hq, decide_false]
      apply beq_eq_false_iff_ne.mpr; intro e'
      have := congrArg BitVec.toNat e'; rw [a1, a2] at this; omega
  unfold AllInAlignedQuantity
  simp only [run_bind, show ((n : Int) ≤b 16) = true by simp; omega, run_sail_assert_true, run_pure, e]
  exact congrArg (fun b => EStateM.Result.ok b s) hb

/-! ## `UserMapped`: Janus' regions are user memory under the ASL's own translation -/

/-- Byte `a` lies in one of `m`'s (well-formed) regions, a writable one if `w`. -/
def InRegion (m : Janus.Arm64.Memory) (a : Nat) (w : Bool) : Prop :=
  ∃ r ∈ m.regions, r.base ≤ a ∧ a < r.base + r.size ∧ r.base + r.size ≤ 2 ^ 48 ∧ (w = false ∨ r.writable = true)

/-- The ASL memory holds Janus' bytes at every address of a region. -/
def MemRel (m : Janus.Arm64.Memory) (s : SState) : Prop :=
  ∀ a, InRegion m a false → s.mem.get? a = some (m.bytes a)

/-- The registers `janus_step` writes before decoding (`stepEntry`). -/
def stepEntryRegs : List Register :=
  [.SEE, .__janus_exc_taken, .__BranchTaken, .__ExclusiveMonitorSet, .__ThisInstrEnc, .__ThisInstr, .__currentCond]

/-- What may change between the start of an instruction and one of its memory accesses: the
general-purpose registers, SP, the step-entry registers, and bytes of the regions. -/
structure TFrame (m : Janus.Arm64.Memory) (s s' : SState) : Prop where
  regs : ∀ r, isGprReg r = false → r ≠ .SP_EL0 → r ∉ stepEntryRegs → s'.regs.get? r = s.regs.get? r
  mem : ∀ a, ¬ InRegion m a false → s'.mem.get? a = s.mem.get? a
  cycle : s'.cycleCount = s.cycleCount
  out : s'.sailOutput = s.sailOutput

/-- A successful translation of `va` to the identity physical address, Normal write-back memory. -/
structure TransOK (d : AddressDescriptor) (va : BitVec 64) : Prop where
  fault : d.fault.statuscode = .Fault_None
  pa : d.paddress.address = va.setWidth 56
  normal : d.memattrs.memtype = .MemType_Normal
  inner : d.memattrs.inner.attrs = MemAttr_WB
  outer : d.memattrs.outer.attrs = MemAttr_WB

/-- LDAR/STLR (`CreateAccDescAcqRel`): acquire for loads, release for stores. -/
def acqRelAcc (w : Bool) : AccessDescriptor := { gprAcc w with acqsc := !w, relsc := w }

/-- LDAPR (`CreateAccDescLDAcqPC`). -/
def acqPCAcc : AccessDescriptor := { gprAcc false with acqpc := true }

/-- LDXR/LDAXR, STXR/STLXR (`CreateAccDescExLDST`). -/
def exclAcc (w acqrel : Bool) : AccessDescriptor :=
  { gprAcc w with exclusive := true, acqsc := acqrel && !w, relsc := acqrel && w }

/-- The access descriptors of ordered and exclusive single-register accesses (tag check cleared). -/
def OrdAcc (w : Bool) (acc : AccessDescriptor) : Prop :=
  acc = acqRelAcc w ∨ (w = false ∧ acc = acqPCAcc) ∨ (∃ ar, acc = exclAcc w ar)

/-- **`UserMapped m s`**: in every state an instruction started in `s` can reach before a memory
access (`TFrame`), the ASL's own `AArch64_TranslateAddress` maps every byte of `m`'s regions
(as an EL0 load, or as a store for writable regions) to the identity physical address as
Normal write-back memory with no fault and without changing the state; and no region byte lies in
the model's GIC or UART windows. This is the hypothesis of the load/store theorems; the check
evaluates it on its tables (`janus-asl-check`, docs/ASL.md). -/
structure UserMapped (m : Janus.Arm64.Memory) (s : SState) : Prop where
  trans : ∀ s', TFrame m s s' → ∀ (va : BitVec 64) (w aligned : Bool) (size : Int), InRegion m va.toNat w →
    ∃ d, (AArch64_TranslateAddress va (gprAcc w) aligned size).run s' = .ok d s' ∧ TransOK d va
  /-- The same for the access descriptors of the ordered and exclusive accesses (`OrdAcc`). -/
  trans_ord : ∀ s', TFrame m s s' → ∀ (va : BitVec 64) (w aligned : Bool) (size : Int) (acc : AccessDescriptor),
    OrdAcc w acc → InRegion m va.toNat w →
    ∃ d, (AArch64_TranslateAddress va acc aligned size).run s' = .ok d s' ∧ TransOK d va
  nodev : ∀ a, InRegion m a false → a / 2 ^ 16 ≠ 0x2C00 ∧ a / 2 ^ 16 ≠ 0x3C00

theorem InRegion.lt {m : Janus.Arm64.Memory} {a : Nat} {w : Bool} (h : InRegion m a w) : a < 2 ^ 48 := by
  obtain ⟨r, _, _, h2, h3, _⟩ := h; omega

theorem InRegion.read {m : Janus.Arm64.Memory} {a : Nat} {w : Bool} (h : InRegion m a w) : InRegion m a false := by
  obtain ⟨r, hr, h1, h2, h3, _⟩ := h; exact ⟨r, hr, h1, h2, h3, Or.inl rfl⟩

/-! ## The physical access -/

theorem pa_window_ne (va : BitVec 64) (hva : va.toNat < 2 ^ 48) (c : BitVec 16) (hc : va.toNat / 2 ^ 16 ≠ c.toNat) :
    (Sail.BitVec.extractLsb (va.setWidth 56) 55 16 == ZeroExtend1 (m := 56 - 1 - 16 + 1) c) = false := by
  apply beq_eq_false_iff_ne.mpr; intro e
  have := congrArg BitVec.toNat e
  have hc' := c.isLt
  simp [Sail.BitVec.extractLsb, ZeroExtend1, Sail.BitVec.zeroExtend, Nat.shiftRight_eq_div_pow] at this
  omega

open Sail.ConcurrencyInterfaceV1.PreSail in
theorem run_PhysMemRead {s : SState} (m : Janus.Arm64.Memory) {d : AddressDescriptor} {va : BitVec 64}
    (hok : TransOK d va) (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (n : Nat) (hn : 0 < n) (acc : AccessDescriptor)
    (hb : ∀ i < n, s.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i))) :
    ∃ v, (PhysMemRead d n acc none).run s = .ok (CreatePhysMemRetStatus .Fault_None, v) s ∧
      v.toNat = m.readLE va.toNat n := by
  obtain ⟨v, hv, hvn⟩ := run_readBytes m n va.toNat hn hb
  refine ⟨v, ?_, hvn⟩
  have g := pa_window_ne va hva GIC_BASE (by simp [GIC_BASE]; omega)
  have u := pa_window_ne va hva UART_BASE (by simp [UART_BASE]; omega)
  have hpa : (va.setWidth 56).toNat = va.toNat := by simp; omega
  unfold PhysMemRead
  simp only [hok.pa, Sail.BitVec.length]
  split
  · next hc => simp only [Bool.and_eq_true] at hc; exact absurd (g.symm.trans hc.2) Bool.false_ne_true
  split
  · next hc => exact absurd (u.symm.trans hc) Bool.false_ne_true
  simp only [run_bind, sail_mem_read, read_request, hpa, hv, run_pure]

section
variable (w : Bool)
theorem gprAcc_acctype : (gprAcc w).acctype = .AccessType_GPR := rfl
theorem gprAcc_el : (gprAcc w).el = 0#2 := rfl
theorem gprAcc_transactional : (gprAcc w).transactional = false := rfl
theorem gprAcc_tagchecked : (gprAcc w).tagchecked = false := rfl
theorem gprAcc_exclusive : (gprAcc w).exclusive = false := rfl
theorem gprAcc_atomicop : (gprAcc w).atomicop = false := rfl
theorem gprAcc_acqsc : (gprAcc w).acqsc = false := rfl
theorem gprAcc_acqpc : (gprAcc w).acqpc = false := rfl
theorem gprAcc_relsc : (gprAcc w).relsc = false := rfl
theorem gprAcc_rcw : (gprAcc w).rcw = false := rfl
theorem gprAcc_ls64 : (gprAcc w).ls64 = false := rfl
theorem gprAcc_write : (gprAcc w).write = w := rfl
end

theorem ss_ns_beq_secure : (SecurityState.SS_NonSecure == SecurityState.SS_Secure) = false := rfl

theorem run_TranslationRegime0 {s : SState} (h : LinuxEL0Config s) :
    (TranslationRegime 0#2).run s = .ok .Regime_EL10 s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [TranslationRegime, EL3, EL2, EL1, EL0, CurrentSecurityState, run_readReg hp, he, run_SecurityStateAtEL0 h,
    run_ELUsingAArch32 h, run_ELIsInHost h, ss_ns_beq_secure]

theorem run_AlignmentEnforced {s : SState} (h : LinuxEL0Config s) : (AlignmentEnforced ()).run s = .ok false s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [AlignmentEnforced, run_readReg hp, he, run_TranslationRegime0 h, run_ELUsingAArch32 h,
    run_readReg h.sctlr1, _get_SCTLR_EL1_Type_A]

theorem run_UnalignedAccessFaults_gpr {s : SState} (h : LinuxEL0Config s) (w tc : Bool) (va : BitVec 64) (n : Int) :
    (AArch64_UnalignedAccessFaults { gprAcc w with tagchecked := tc } va n).run s = .ok false s := by
  cfg_simp [AArch64_UnalignedAccessFaults, run_AlignmentEnforced h, gprAcc_acctype, gprAcc_rcw, gprAcc_ls64,
    gprAcc_exclusive, gprAcc_atomicop, gprAcc_acqsc, gprAcc_acqpc, gprAcc_relsc]

theorem run_BigEndian_gpr {s : SState} (h : LinuxEL0Config s) :
    (BigEndian .AccessType_GPR).run s = .ok false s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [BigEndian, HaveNV2Ext, run_IsFeatureImplemented h, run_UsingAArch32 h, run_readReg hp, he, EL0,
    SCTLR_read__1, S1TranslationRegime__1, run_S1TranslationRegime h, SCTLR_read, EL1, run_readReg h.sctlr1,
    Mk_SCTLRType, _get_SCTLRType_E0E]

theorem gprAcc_tc (w : Bool) : ({ gprAcc w with tagchecked := false } : AccessDescriptor) = gprAcc w := rfl

theorem run_AccessIsTagChecked_gpr {t : SState} (hc : LinuxEL0Config t) (va : BitVec 64) (w : Bool) :
    (AArch64_AccessIsTagChecked va { gprAcc w with tagchecked := true }).run t = .ok false t :=
  run_AccessIsTagChecked hc va _ rfl rfl (by cases w <;> simp [gprAcc])

theorem run_MemSingle_read {t : SState} (m : Janus.Arm64.Memory) (hc : LinuxEL0Config t) {va : BitVec 64} {n : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16) (hq : va.toNat % 16 + n ≤ 16) (tc aligned : Bool)
    (hT : ∃ d, (AArch64_TranslateAddress va (gprAcc false) aligned (n : Int)).run t = .ok d t ∧ TransOK d va)
    (hva : va.toNat < 2 ^ 48) (hdev : va.toNat / 2 ^ 16 ≠ 0x2C00 ∧ va.toNat / 2 ^ 16 ≠ 0x3C00)
    (hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i))) :
    ∃ v, (AArch64_MemSingle_read__1 va n { gprAcc false with tagchecked := tc } aligned false).run t = .ok v t ∧
      v.toNat = m.readLE va.toNat n := by
  obtain ⟨d, hd, hok⟩ := hT
  have hn0 : 0 < n := by omega
  obtain ⟨v, hv, hvn⟩ := run_PhysMemRead m hok hva hdev n hn0 (gprAcc false) hb
  have hsz : ((n == 1) || ((n == 2) || ((n == 4) || ((n == 8) || (n == 16))))) = true := by
    rcases hn with h | h | h | h | h <;> subst h <;> rfl
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  rw [decide_eq_true hq] at hai
  unfold AArch64_MemSingle_read__1
  cases tc <;>
  cfg_simp [hsz, HaveLSE2Ext, run_IsFeatureImplemented hc, hai, HaveMTE2Ext, run_AccessIsTagChecked_gpr hc,
    gprAcc_tc, hd, IsFault, hok.fault, HaveTME, run_readReg hc.speInFlight, hok.normal, hok.inner, hok.outer, hv,
    IsFault__2, CreatePhysMemRetStatus]
  all_goals simp only [gprAcc_transactional, gprAcc_tagchecked]
  all_goals cfg_simp [run_IsFeatureImplemented hc, run_readReg hc.speInFlight, undefined_PhysMemRetStatus,
    undefined_ErrorState, undefined_Fault, run_internal_pick, hv, CreatePhysMemRetStatus]
  all_goals rw [Nat.mod_eq_of_lt (by rw [show n * 8 = 8 * n from Nat.mul_comm n 8]; exact v.isLt), hvn]

/-! ## Byte loops -/
theorem updateSubrange'_toNat_low {N : Nat} (x : BitVec N) (lo len : Nat) (y : BitVec len)
    (hlen : lo + len ≤ N) (hx : x.toNat < 2 ^ lo) :
    (Sail.BitVec.updateSubrange' x lo len y).toNat = x.toNat + y.toNat * 2 ^ lo := by
  have hy := y.isLt
  have hb : x.toNat + y.toNat * 2 ^ lo < 2 ^ N := by
    have : (y.toNat + 1) * 2 ^ lo ≤ 2 ^ len * 2 ^ lo := Nat.mul_le_mul_right _ hy
    have : 2 ^ len * 2 ^ lo = 2 ^ (lo + len) := by rw [← Nat.pow_add, Nat.add_comm]
    have : 2 ^ (lo + len) ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hlen
    rw [Nat.add_mul] at *; omega
  have e : Sail.BitVec.updateSubrange' x lo len y = BitVec.ofNat N (x.toNat + y.toNat * 2 ^ lo) := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [getLsbD_updateSubrange' x lo len y k hlen, BitVec.getLsbD_ofNat]
    rw [show x.toNat + y.toNat * 2 ^ lo = y.toNat <<< lo ||| x.toNat by
      rw [← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]]
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases h1 : lo ≤ k ∧ k < lo + len
    · rw [if_pos h1]
      have : x.toNat.testBit k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h1.1))
      simp [h1.1, this, BitVec.getLsbD]
    · rw [if_neg h1]
      by_cases h2 : lo ≤ k
      · have hk2 : lo + len ≤ k := by omega
        have : y.toNat.testBit (k - lo) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
        have : x.toNat.testBit k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h2))
        simp [h2, *, BitVec.getLsbD]
      · simp [h2, BitVec.getLsbD]
  rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

theorem readLE_lt (m : Janus.Arm64.Memory) (a n : Nat) : m.readLE a n < 2 ^ (8 * n) := by
  induction n generalizing a with
  | zero => simp [Janus.Arm64.Memory.readLE]
  | succ n ih =>
    simp only [Janus.Arm64.Memory.readLE]
    have h1 := ih (a + 1)
    have h2 := (m.bytes a).isLt
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add]
    have : 2 ^ 8 = 256 := rfl
    omega

theorem readLE_succ_high (m : Janus.Arm64.Memory) (a n : Nat) :
    m.readLE a (n + 1) = m.readLE a n + (m.bytes (a + n)).toNat * 2 ^ (8 * n) := by
  induction n generalizing a with
  | zero => simp [Janus.Arm64.Memory.readLE]
  | succ n ih =>
    rw [Janus.Arm64.Memory.readLE, ih (a + 1), Janus.Arm64.Memory.readLE]
    rw [show a + 1 + n = a + (n + 1) by omega, show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add]
    have : 2 ^ 8 = 256 := rfl
    rw [this, Nat.mul_add, Nat.mul_left_comm]; omega

theorem updateSubrange_byte_toNat {N : Nat} (b : BitVec N) (hi lo : Nat) (y : BitVec (1 * 8)) (hlo : hi = lo + 7)
    (hN : lo + 8 ≤ N) (hb : b.toNat < 2 ^ lo) :
    (Sail.BitVec.updateSubrange b hi lo (BitVec.setWidth (hi - lo + 1) y)).toNat = b.toNat + y.toNat * 2 ^ lo := by
  subst hlo
  rw [Sail.BitVec.updateSubrange, updateSubrange'_toNat_low _ _ _ _ (by omega) hb, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by have := y.isLt; rw [show lo + 7 - lo + 1 = 1 * 8 by omega]; exact this)]

/-- The byte loop of `Mem_read` (an access that crosses a 16-byte boundary): byte `i` of the
result is the 1-byte read at `address + i`. -/
theorem run_byteLoop_read {t : SState} (m : Janus.Arm64.Memory) (A : AccessDescriptor) (al : Bool) (va : BitVec 64)
    (n : Nat) (hn : 1 ≤ n) (hn16 : n ≤ 16)
    (h1 : ∀ i : Int, 1 ≤ i → i ≤ (n : Int) - 1 → (AArch64_MemSingle_read (Sail.BitVec.addInt va i) 1 A al).run t =
      .ok (BitVec.ofNat (1 * 8) (m.bytes (va.toNat + i.toNat)).toNat) t)
    (init : BitVec (n * 8)) (hinit : init.toNat = m.readLE va.toNat 1) :
    ∃ v, (forIn ({ start := 1, stop := (n : Int) - 1, step_pos := by decide } : IntRange) init
        (fun i (b : BitVec (n * 8)) =>
          (fun (x : BitVec (1 * 8)) => ForInStep.yield (Sail.BitVec.updateSubrange b (8 * i + 7).toNat (8 * i).toNat
            x)) <$>
          AArch64_MemSingle_read (Sail.BitVec.addInt va i) 1 A al)).run t = .ok v t ∧ v.toNat = m.readLE va.toNat n := by
  let g : Int → BitVec (n * 8) → BitVec (n * 8) := fun i b =>
    Sail.BitVec.updateSubrange b (8 * i + 7).toNat (8 * i).toNat
      (BitVec.ofNat (1 * 8) (m.bytes (va.toNat + i.toNat)).toNat)
  let P : Int → BitVec (n * 8) → Prop := fun i b => b.toNat = m.readLE va.toNat i.toNat
  have hstep : ∀ i b, 1 ≤ i → i ≤ (n : Int) - 1 → P i b → P (i + 1) (g i b) := by
    intro i b hi1 hi2 hp
    simp only [P, g] at hp ⊢
    obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
    simp only [Int.toNat_natCast, show ((k : Int) + 1).toNat = k + 1 by omega] at hp ⊢
    rw [updateSubrange_byte_toNat _ _ _ _ (by omega) (by omega)
      (by rw [hp, show (8 * (k : Int)).toNat = 8 * k by omega]; exact readLE_lt m _ _)]
    rw [readLE_succ_high, hp, show (8 * (k : Int)).toNat = 8 * k by omega]
    simp
  have h0 : P 1 init := by simp only [P]; exact hinit
  refine ⟨intFold g 1 ((n : Int) - 1) init, ?_, ?_⟩
  · apply run_forIn_inv 1 ((n : Int) - 1) _ init _ g P t h0
    intro i b hi1 hi2 hp
    refine ⟨?_, hstep i b hi1 hi2 hp⟩
    simp only [run_map, h1 i hi1 hi2]; rfl
  · have := intFold_inv g P 1 ((n : Int) - 1) init (by omega) h0 hstep
    simp only [P, show ((n : Int) - 1 + 1).toNat = n by omega] at this
    exact this

theorem accessible_bytes {m : Janus.Arm64.Memory} {a n : Nat} {w : Bool} (h : m.accessible a n w = true) :
    ∀ i < n, InRegion m (a + i) w := by
  intro i hi
  simp only [Janus.Arm64.Memory.accessible, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨r, hr, ⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩ := h
  refine ⟨r, hr, by omega, by omega, h3, ?_⟩
  cases w
  · exact Or.inl rfl
  · simp at h4; exact Or.inr h4

theorem accessible_lt {m : Janus.Arm64.Memory} {a n : Nat} {w : Bool} (h : m.accessible a n w = true) :
    a + n ≤ 2 ^ 48 := by
  simp only [Janus.Arm64.Memory.accessible, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨r, hr, ⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩ := h
  omega

theorem addInt_toNat (va : BitVec 64) (i : Nat) (h : va.toNat + i < 2 ^ 64) :
    (Sail.BitVec.addInt va (i : Int)).toNat = va.toNat + i := by
  simp only [Sail.BitVec.addInt, BitVec.toNat_add, BitVec.toNat_ofInt]
  have : ((i : Int) % (2 ^ 64 : Nat)).toNat = i % 2 ^ 64 := by omega
  rw [this]; omega

/-- A 1-byte read of a region byte (the elements of `Mem_read`'s byte loop). -/
theorem run_MemSingle_read_byte {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (hM : MemRel m t) (va : BitVec 64) (hr : InRegion m va.toNat false) (tc al : Bool) :
    (AArch64_MemSingle_read va 1 { gprAcc false with tagchecked := tc } al).run t =
      .ok (BitVec.ofNat (1 * 8) (m.bytes va.toNat).toNat) t := by
  obtain ⟨v, hv, hvn⟩ := run_MemSingle_read m hc (n := 1) (Or.inl rfl) (by omega) tc al
    (hU.trans t hf va false al 1 hr) hr.lt (hU.nodev _ hr) (fun i hi => by
      rw [show i = 0 by omega, Nat.add_zero]; exact hM _ hr)
  rw [AArch64_MemSingle_read, hv]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hvn]; simp [Janus.Arm64.Memory.readLE]

theorem run_Mem_read {s t : SState} {m : Janus.Arm64.Memory} (hU : UserMapped m s) (hf : TFrame m s t)
    (hc : LinuxEL0Config t) (hM : MemRel m t) (va : BitVec 64) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (hacc : m.accessible va.toNat n false = true) (tc : Bool) :
    ∃ v, (Mem_read va n { gprAcc false with tagchecked := tc }).run t = .ok v t ∧ v.toNat = m.readLE va.toNat n := by
  have hreg := accessible_bytes hacc
  have hlt := accessible_lt hacc
  have hr0 : InRegion m va.toNat false := by have := hreg 0 (by omega); rwa [Nat.add_zero] at this
  have hb : ∀ i < n, t.mem.get? (va.toNat + i) = some (m.bytes (va.toNat + i)) := fun i hi => hM _ (hreg i hi)
  have hsz2 : (n == 1 || n == 2 || n == 4 || n == 8 || n == 16) = true := by
    rcases hn with h | h | h | h <;> subst h <;> rfl
  have hal := isAligned_iff va n (by omega)
  have hai := run_AllInAlignedQuantity t va n (by omega) (by omega) (by omega)
  have hU1 := run_UnalignedAccessFaults_gpr hc false tc va n
  have hat : ({ gprAcc false with tagchecked := tc } : AccessDescriptor).acctype = .AccessType_GPR := rfl
  by_cases hq : va.toNat % 16 + n ≤ 16
  · obtain ⟨v, hv, hvn⟩ := run_MemSingle_read m hc (n := n) (by omega) hq tc (IsAligned__1 va n)
      (hU.trans t hf va false _ n hr0) hr0.lt (hU.nodev _ hr0) hb
    rw [decide_eq_true hq] at hai
    refine ⟨v, ?_, hvn⟩
    unfold Mem_read Mem_read__2
    generalize ({ gprAcc false with tagchecked := tc } : AccessDescriptor) = A at hU1 hat hv ⊢
    cases ha : IsAligned__1 va (n : Int) <;> rw [ha] at hv <;>
    cfg_simp [hsz2, undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
      run_BigEndian_gpr hc, ha, hv, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl]
  · rw [decide_eq_false hq] at hai
    have hn2 : n = 2 ∨ n = 4 ∨ n = 8 := by omega
    have hna : IsAligned__1 va (n : Int) = false := by
      rw [hal]; apply decide_eq_false; intro h0; apply hq
      rcases hn2 with h | h | h <;> subst h <;> omega
    have h0 := run_MemSingle_read_byte hU hf hc hM va hr0 tc false
    have h1 : ∀ i : Int, 1 ≤ i → i ≤ (n : Int) - 1 →
        (AArch64_MemSingle_read (Sail.BitVec.addInt va i) 1 { gprAcc false with tagchecked := tc } true).run t =
          .ok (BitVec.ofNat (1 * 8) (m.bytes (va.toNat + i.toNat)).toNat) t := by
      intro i hi1 hi2
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      have ha := addInt_toNat va k (by omega)
      have hrk := hreg k (by omega)
      rw [← ha] at hrk
      rw [run_MemSingle_read_byte hU hf hc hM _ hrk tc true, ha, Int.toNat_natCast]
    have hinit : (Sail.BitVec.updateSubrange (0#(n * 8)) 7 0 (m.bytes va.toNat)).toNat = m.readLE va.toNat 1 := by
      rw [Sail.BitVec.updateSubrange, updateSubrange'_toNat_low _ _ _ _ (by omega) (by simp)]
      simp [Janus.Arm64.Memory.readLE]
    obtain ⟨v, hv, hvn⟩ := run_byteLoop_read m { gprAcc false with tagchecked := tc } true va n (by omega) (by omega)
      h1 _ hinit
    refine ⟨v, ?_, hvn⟩
    unfold Mem_read Mem_read__2
    generalize ({ gprAcc false with tagchecked := tc } : AccessDescriptor) = A at hU1 hat h0 h1 hv ⊢
    rcases hn2 with rfl | rfl | rfl <;> simp only [Int.cast_ofNat_Int, Int.reduceSub, Nat.reduceMul] at hna hai hU1 h1 hv <;>
    cfg_simp [hsz2, undefined_Constraint, run_internal_pick, hU1, hat, HaveLSE2Ext, run_IsFeatureImplemented hc, hai,
      run_BigEndian_gpr hc, hna, h0, show (AccessType.AccessType_GPR == AccessType.AccessType_ASIMD) = false from rfl,
      ConstrainUnpredictable, __UNKNOWN_Constraint, HaveLRCPC3Ext,
      show Int.ediv 2 2 = 1 from rfl, show Int.ediv 4 2 = 2 from rfl, show Int.ediv 8 2 = 4 from rfl,
      show (Constraint.Constraint_NONE == Constraint.Constraint_NONE) = true from rfl,
      show (Constraint.Constraint_NONE == Constraint.Constraint_FAULT) = false from rfl]
    all_goals erw [hv]
    all_goals simp only [run_BigEndian_gpr hc, Bool.false_eq_true, ite_false, run_pure]

end JanusASL.Proofs