import JanusASL.Proofs.Step
import JanusASL.Proofs.CfgDef

/-! # `LinuxEL0Config`: the machine configured as Linux EL0, as `janus_init` sets it up

The branch path of the ASL (`BranchTo`, `BranchNotTaken`) consults the BRBE, SPE, GCS and TBI
configuration. `LinuxEL0Config s` fixes the configuration registers it reads to the values
`janus_init` gives them (dumped by `janus-asl-check --cfg`; the check asserts the predicate on its
base state and every post-state). -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

-- The configuration registers' field getters, evaluated by `simp` on the fixed values.
attribute [local simp] Mk_SCRType Sail.BitVec.extractLsb
attribute [local simp] _get_BRBCR_EL1_Type_CC _get_BRBCR_EL1_Type_E0BRE _get_BRBCR_EL1_Type_E1BRE _get_BRBCR_EL1_Type_MPRED _get_BRBCR_EL2_Type_CC _get_BRBCR_EL2_Type_E0HBRE
attribute [local simp] _get_BRBCR_EL2_Type_E2BRE _get_BRBCR_EL2_Type_MPRED _get_BRBFCR_EL1_Type_BANK _get_BRBFCR_EL1_Type_CONDDIR _get_BRBFCR_EL1_Type_DIRCALL _get_BRBFCR_EL1_Type_DIRECT
attribute [local simp] _get_BRBFCR_EL1_Type_EnI _get_BRBFCR_EL1_Type_INDCALL _get_BRBFCR_EL1_Type_INDIRECT _get_BRBFCR_EL1_Type_LASTFAILED _get_BRBFCR_EL1_Type_PAUSED _get_BRBFCR_EL1_Type_RTN
attribute [local simp] _get_GCSCRE0_EL1_Type_PCRSEL _get_GCSCRE0_EL1_Type_RVCHKEN _get_HCR_EL2_Type_AMO _get_HCR_EL2_Type_API _get_HCR_EL2_Type_ATA
attribute [local simp] _get_HCR_EL2_Type_CD _get_HCR_EL2_Type_DC _get_HCR_EL2_Type_DCT _get_HCR_EL2_Type_E2H
attribute [local simp] _get_HCR_EL2_Type_FMO _get_HCR_EL2_Type_FWB _get_HCR_EL2_Type_GPF _get_HCR_EL2_Type_ID _get_HCR_EL2_Type_IMO _get_HCR_EL2_Type_NV
attribute [local simp] _get_HCR_EL2_Type_NV1 _get_HCR_EL2_Type_PTW _get_HCR_EL2_Type_RW _get_HCR_EL2_Type_TDZ
attribute [local simp] _get_HCR_EL2_Type_TEA _get_HCR_EL2_Type_TGE _get_HCR_EL2_Type_TID3
attribute [local simp] _get_HCR_EL2_Type_TIDCP _get_HCR_EL2_Type_TWE _get_HCR_EL2_Type_TWEDEL _get_HCR_EL2_Type_TWEDEn
attribute [local simp] _get_HCR_EL2_Type_TWI _get_HCR_EL2_Type_VF _get_HCR_EL2_Type_VI _get_HCR_EL2_Type_VM _get_HCR_EL2_Type_VSE _get_HCRX_EL2_Type_CMOW
attribute [local simp] _get_HCRX_EL2_Type_FnXS _get_HCRX_EL2_Type_GCSEn _get_HCRX_EL2_Type_SCTLR2En _get_HCRX_EL2_Type_TALLINT _get_HCRX_EL2_Type_TCR2En _get_HCRX_EL2_Type_TMEA
attribute [local simp] _get_HCRX_EL2_Type_VFNMI _get_HCRX_EL2_Type_VINMI _get_MDCR_EL2_Type_E2PB _get_MDCR_EL2_Type_EBWE _get_MDCR_EL2_Type_HCCD
attribute [local simp] _get_MDCR_EL2_Type_HPMD _get_MDCR_EL2_Type_HPME _get_MDCR_EL2_Type_HPMFZO _get_MDCR_EL2_Type_HPMN
attribute [local simp] _get_MDCR_EL2_Type_TDE
attribute [local simp] _get_MDCR_EL3_Type_E3BREC _get_MDCR_EL3_Type_E3BREW _get_MDCR_EL3_Type_EBWE
attribute [local simp] _get_MDCR_EL3_Type_MCCD _get_MDCR_EL3_Type_MPMX _get_MDCR_EL3_Type_NSPB _get_MDCR_EL3_Type_NSPBE _get_MDCR_EL3_Type_SBRBE
attribute [local simp] _get_MDCR_EL3_Type_SCCD _get_MDCR_EL3_Type_SDD _get_MDCR_EL3_Type_SPME
attribute [local simp] _get_PMBLIMITR_EL1_Type_E _get_PMBSR_EL1_Type_S _get_PMSCR_EL1_Type_E0SPE _get_PMSCR_EL1_Type_E1SPE
attribute [local simp] _get_PMSCR_EL1_Type_PA _get_PMSCR_EL2_Type_E0HSPE _get_PMSCR_EL2_Type_E2SPE _get_PMSCR_EL2_Type_PA _get_PMSIDR_EL1_Type_PBT
attribute [local simp] _get_SCR_EL3_Type_API _get_SCR_EL3_Type_ATA _get_SCR_EL3_Type_EA
attribute [local simp] _get_SCR_EL3_Type_EASE _get_SCR_EL3_Type_EEL2 _get_SCR_EL3_Type_FGTEn
attribute [local simp] _get_SCR_EL3_Type_FIQ _get_SCR_EL3_Type_GCSEn _get_SCR_EL3_Type_GPF _get_SCR_EL3_Type_HXEn
attribute [local simp] _get_SCR_EL3_Type_IRQ _get_SCR_EL3_Type_NMEA _get_SCR_EL3_Type_NS _get_SCR_EL3_Type_NSE
attribute [local simp] _get_SCR_EL3_Type_RW _get_SCR_EL3_Type_SCTLR2En _get_SCR_EL3_Type_SIF _get_SCR_EL3_Type_TCR2En
attribute [local simp] _get_SCR_EL3_Type_TMEA _get_SCR_EL3_Type_TWE _get_SCR_EL3_Type_TWEDEL _get_SCR_EL3_Type_TWEDEn
attribute [local simp] _get_SCR_EL3_Type_TWI _get_SCR_Type_AW _get_SCR_Type_EA _get_SCRType_EA _get_SCR_Type_FIQ
attribute [local simp] _get_SCRType_FIQ _get_SCR_Type_FW _get_SCR_Type_IRQ _get_SCRType_IRQ _get_SCR_Type_NS _get_SCRType_NS
attribute [local simp] _get_TCR_EL1_Type_A1 _get_TCR_EL1_Type_AS _get_TCR_EL1_Type_DS _get_TCR_EL1_Type_E0PD0 _get_TCR_EL1_Type_E0PD1 _get_TCR_EL1_Type_EPD0
attribute [local simp] _get_TCR_EL1_Type_EPD1 _get_TCR_EL1_Type_HA _get_TCR_EL1_Type_HD _get_TCR_EL1_Type_HPD0 _get_TCR_EL1_Type_HPD1 _get_TCR_EL1_Type_IPS
attribute [local simp] _get_TCR_EL1_Type_IRGN0 _get_TCR_EL1_Type_IRGN1 _get_TCR_EL1_Type_MTX0 _get_TCR_EL1_Type_MTX1 _get_TCR_EL1_Type_NFD0 _get_TCR_EL1_Type_NFD1
attribute [local simp] _get_TCR_EL1_Type_ORGN0 _get_TCR_EL1_Type_ORGN1 _get_TCR_EL1_Type_SH0 _get_TCR_EL1_Type_SH1 _get_TCR_EL1_Type_T0SZ _get_TCR_EL1_Type_T1SZ
attribute [local simp] _get_TCR_EL1_Type_TBI0 _get_TCR_EL1_Type_TBI1 _get_TCR_EL1_Type_TBID0 _get_TCR_EL1_Type_TBID1 _get_TCR_EL1_Type_TCMA0 _get_TCR_EL1_Type_TCMA1
attribute [local simp] _get_TCR_EL1_Type_TG0 _get_TCR_EL1_Type_TG1

set_option maxRecDepth 100000

theorem run_IsFeatureImplemented {s : SState} (h : LinuxEL0Config s) (f : Feature) :
    (IsFeatureImplemented f).run s = .ok (cfgFeat f) s := by
  obtain ⟨v, hv, hf⟩ := h.fi
  simp only [IsFeatureImplemented, run_bind, run_readReg hv, run_pure, hf]

/-- `simp` with the configuration's evaluation lemmas. -/
syntax "cfg_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cfg_simp [$ls,*]) => `(tactic| simp (config := { decide := true }) [cfgFeat, num_of_Feature,
      cfgFeaturesOff, run_bind, run_pure, run_map, run_sail_assert_true, run_undefined_bool, run_undefined_bitvector,
      run_undefined_int, HaveEL, orM, andM, toBool, $ls,*])
  | `(tactic| cfg_simp) => `(tactic| cfg_simp [])

theorem run_UsingAArch32 {s : SState} (h : LinuxEL0Config s) : (UsingAArch32 ()).run s = .ok false s := by
  obtain ⟨p, hp, _, hrw, _⟩ := h.pstate
  cfg_simp [UsingAArch32, HaveAArch64, run_readReg hp, hrw, run_IsFeatureImplemented h, HaveAArch32]

theorem run_HaveAArch64 {s : SState} (h : LinuxEL0Config s) : (HaveAArch64 ()).run s = .ok true s := by
  cfg_simp [HaveAArch64, run_IsFeatureImplemented h]

theorem run_HaveSecureEL2Ext {s : SState} (h : LinuxEL0Config s) : (HaveSecureEL2Ext ()).run s = .ok true s := by
  cfg_simp [HaveSecureEL2Ext, run_IsFeatureImplemented h]

theorem run_SCR_GEN_read {s : SState} (h : LinuxEL0Config s) :
    (SCR_GEN_read ()).run s = .ok (Mk_SCRType 0x24006030401#64) s := by
  cfg_simp [SCR_GEN_read, run_HaveAArch64 h, run_readReg h.scr3]

theorem run_IsSecureBelowEL3 {s : SState} (h : LinuxEL0Config s) : (IsSecureBelowEL3 ()).run s = .ok false s := by
  cfg_simp [IsSecureBelowEL3, run_SCR_GEN_read h]

theorem run_ELUsingAArch32 {s : SState} (h : LinuxEL0Config s) (el : BitVec 2) :
    (ELUsingAArch32 el).run s = .ok false s := by
  obtain ⟨p, hp, he, hrw, _⟩ := h.pstate
  have : el = 0#2 ∨ el = 1#2 ∨ el = 2#2 ∨ el = 3#2 := by revert el; decide
  rcases this with rfl | rfl | rfl | rfl <;>
  cfg_simp [ELUsingAArch32, ELStateUsingAArch32, ELStateUsingAArch32K, run_IsSecureBelowEL3 h, HaveAArch32EL,
    run_HaveAArch64 h, run_HaveSecureEL2Ext h, run_readReg h.scr3, run_readReg h.hcr2, run_readReg hp, he, hrw,
    __UNKNOWN_boolean, run_IsFeatureImplemented h, HaveVirtHostExt]

theorem run_IsSecureEL2Enabled {s : SState} (h : LinuxEL0Config s) : (IsSecureEL2Enabled ()).run s = .ok false s := by
  cfg_simp [IsSecureEL2Enabled, run_HaveSecureEL2Ext h, run_ELUsingAArch32 h, run_readReg h.scr3]

theorem run_EL2Enabled {s : SState} (h : LinuxEL0Config s) : (EL2Enabled ()).run s = .ok true s := by
  cfg_simp [EL2Enabled, run_SCR_GEN_read h, run_IsSecureEL2Enabled h]

theorem run_ELIsInHost {s : SState} (h : LinuxEL0Config s) (el : BitVec 2) :
    (ELIsInHost el).run s = .ok false s := by
  have : el = 0#2 ∨ el = 1#2 ∨ el = 2#2 ∨ el = 3#2 := by revert el; decide
  rcases this with rfl | rfl | rfl | rfl <;>
  cfg_simp [ELIsInHost, HaveVirtHostExt, run_IsFeatureImplemented h, run_ELUsingAArch32 h, run_EL2Enabled h,
    run_readReg h.hcr2]

theorem run_S1TranslationRegime {s : SState} (h : LinuxEL0Config s) :
    (S1TranslationRegime 0#2).run s = .ok 1#2 s := by
  cfg_simp [S1TranslationRegime, run_ELUsingAArch32 h, HaveVirtHostExt, run_IsFeatureImplemented h,
    run_ELIsInHost h, EL0, EL1]

theorem access_cases {N : Nat} (v : BitVec N) (i : Nat) :
    Sail.BitVec.access v i = 0#1 ∨ Sail.BitVec.access v i = 1#1 := by
  generalize Sail.BitVec.access v i = b; revert b; decide

theorem run_EffectiveTBI {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) :
    (EffectiveTBI v true 0#2).run s = .ok (if Sail.BitVec.access v 55 == 1#1 then 0#1 else 1#1) s := by
  rcases access_cases v 55 with hb | hb <;>
  cfg_simp [EffectiveTBI, run_S1TranslationRegime h, run_ELUsingAArch32 h, hb, run_readReg h.tcr1,
    HavePACExt, run_IsFeatureImplemented h, EL1, EL2, EL3]

theorem run_AddrTop {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) :
    (AddrTop v true 0#2).run s = .ok (if Sail.BitVec.access v 55 == 1#1 then 63 else 55) s := by
  rcases access_cases v 55 with hb | hb <;>
  cfg_simp [AddrTop, run_S1TranslationRegime h, run_ELUsingAArch32 h, run_EffectiveTBI h, hb]

theorem run_IsInHost {s : SState} (h : LinuxEL0Config s) : (IsInHost ()).run s = .ok false s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [IsInHost, run_readReg hp, he, run_ELIsInHost h]

theorem run_AArch64_BranchAddr {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) (hv : v.toNat < 2 ^ 56) :
    (AArch64_BranchAddr v 0#2).run s = .ok v s := by
  rcases access_cases v 55 with hb | hb
  · cfg_simp [AArch64_BranchAddr, run_UsingAArch32 h, run_AddrTop h, hb, EL0, EL1]
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.zeroExtend, BitVec.extractLsb_toNat]
    omega
  · cfg_simp [AArch64_BranchAddr, run_UsingAArch32 h, run_AddrTop h, hb]

theorem run_BranchRecordAllowed {s : SState} (h : LinuxEL0Config s) :
    (BranchRecordAllowed 0#2).run s = .ok false s := by
  cfg_simp [BranchRecordAllowed, run_ELUsingAArch32 h, run_readReg h.brbfcr1, run_readReg h.mdcr3, HaveBRBEv1p1,
    run_IsFeatureImplemented h, EL3, EL2, EL1, EL0]

theorem run_BRBEBranch {s : SState} (h : LinuxEL0Config s) (bt : BranchType) (c : Bool) (t : BitVec 64) :
    (BRBEBranch bt c t).run s = .ok () (s.set .__last_branch_valid false) := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [BRBEBranch, run_readReg hp, he, run_BranchRecordAllowed h]

theorem run_internal_pick {α : Type} (a : α) (l : List α) (s : SState) :
    (internal_pick (a :: l) : SailM α).run s = .ok a s := by
  cases s; rfl

/-- `SecurityState` (in)equalities, as the generated `BEq` computes them. -/
@[local simp] theorem ss_beq_SS_NonSecure_SS_NonSecure : (SecurityState.SS_NonSecure == SecurityState.SS_NonSecure) = true := rfl
@[local simp] theorem ss_bne_SS_NonSecure_SS_NonSecure : (SecurityState.SS_NonSecure != SecurityState.SS_NonSecure) = false := rfl
@[local simp] theorem ss_beq_SS_NonSecure_SS_Root : (SecurityState.SS_NonSecure == SecurityState.SS_Root) = false := rfl
@[local simp] theorem ss_bne_SS_NonSecure_SS_Root : (SecurityState.SS_NonSecure != SecurityState.SS_Root) = true := rfl
@[local simp] theorem ss_beq_SS_NonSecure_SS_Realm : (SecurityState.SS_NonSecure == SecurityState.SS_Realm) = false := rfl
@[local simp] theorem ss_bne_SS_NonSecure_SS_Realm : (SecurityState.SS_NonSecure != SecurityState.SS_Realm) = true := rfl
@[local simp] theorem ss_beq_SS_NonSecure_SS_Secure : (SecurityState.SS_NonSecure == SecurityState.SS_Secure) = false := rfl
@[local simp] theorem ss_bne_SS_NonSecure_SS_Secure : (SecurityState.SS_NonSecure != SecurityState.SS_Secure) = true := rfl
@[local simp] theorem ss_beq_SS_Root_SS_NonSecure : (SecurityState.SS_Root == SecurityState.SS_NonSecure) = false := rfl
@[local simp] theorem ss_bne_SS_Root_SS_NonSecure : (SecurityState.SS_Root != SecurityState.SS_NonSecure) = true := rfl
@[local simp] theorem ss_beq_SS_Root_SS_Root : (SecurityState.SS_Root == SecurityState.SS_Root) = true := rfl
@[local simp] theorem ss_bne_SS_Root_SS_Root : (SecurityState.SS_Root != SecurityState.SS_Root) = false := rfl
@[local simp] theorem ss_beq_SS_Root_SS_Realm : (SecurityState.SS_Root == SecurityState.SS_Realm) = false := rfl
@[local simp] theorem ss_bne_SS_Root_SS_Realm : (SecurityState.SS_Root != SecurityState.SS_Realm) = true := rfl
@[local simp] theorem ss_beq_SS_Root_SS_Secure : (SecurityState.SS_Root == SecurityState.SS_Secure) = false := rfl
@[local simp] theorem ss_bne_SS_Root_SS_Secure : (SecurityState.SS_Root != SecurityState.SS_Secure) = true := rfl
@[local simp] theorem ss_beq_SS_Realm_SS_NonSecure : (SecurityState.SS_Realm == SecurityState.SS_NonSecure) = false := rfl
@[local simp] theorem ss_bne_SS_Realm_SS_NonSecure : (SecurityState.SS_Realm != SecurityState.SS_NonSecure) = true := rfl
@[local simp] theorem ss_beq_SS_Realm_SS_Root : (SecurityState.SS_Realm == SecurityState.SS_Root) = false := rfl
@[local simp] theorem ss_bne_SS_Realm_SS_Root : (SecurityState.SS_Realm != SecurityState.SS_Root) = true := rfl
@[local simp] theorem ss_beq_SS_Realm_SS_Realm : (SecurityState.SS_Realm == SecurityState.SS_Realm) = true := rfl
@[local simp] theorem ss_bne_SS_Realm_SS_Realm : (SecurityState.SS_Realm != SecurityState.SS_Realm) = false := rfl
@[local simp] theorem ss_beq_SS_Realm_SS_Secure : (SecurityState.SS_Realm == SecurityState.SS_Secure) = false := rfl
@[local simp] theorem ss_bne_SS_Realm_SS_Secure : (SecurityState.SS_Realm != SecurityState.SS_Secure) = true := rfl
@[local simp] theorem ss_beq_SS_Secure_SS_NonSecure : (SecurityState.SS_Secure == SecurityState.SS_NonSecure) = false := rfl
@[local simp] theorem ss_bne_SS_Secure_SS_NonSecure : (SecurityState.SS_Secure != SecurityState.SS_NonSecure) = true := rfl
@[local simp] theorem ss_beq_SS_Secure_SS_Root : (SecurityState.SS_Secure == SecurityState.SS_Root) = false := rfl
@[local simp] theorem ss_bne_SS_Secure_SS_Root : (SecurityState.SS_Secure != SecurityState.SS_Root) = true := rfl
@[local simp] theorem ss_beq_SS_Secure_SS_Realm : (SecurityState.SS_Secure == SecurityState.SS_Realm) = false := rfl
@[local simp] theorem ss_bne_SS_Secure_SS_Realm : (SecurityState.SS_Secure != SecurityState.SS_Realm) = true := rfl
@[local simp] theorem ss_beq_SS_Secure_SS_Secure : (SecurityState.SS_Secure == SecurityState.SS_Secure) = true := rfl
@[local simp] theorem ss_bne_SS_Secure_SS_Secure : (SecurityState.SS_Secure != SecurityState.SS_Secure) = false := rfl

theorem run_ProfilingBufferEnabled {s : SState} (h : LinuxEL0Config s) :
    (ProfilingBufferEnabled ()).run s = .ok false s := by
  cfg_simp [ProfilingBufferEnabled, ProfilingBufferOwner, HaveStatisticalProfiling, HaveRME, run_IsFeatureImplemented h,
    run_readReg h.mdcr3, run_readReg h.mdcr2, run_readReg h.scr3, run_readReg h.pmblimitr1, run_readReg h.pmbsr1,
    run_ELUsingAArch32 h, run_IsSecureEL2Enabled h, run_HaveSecureEL2Ext h, EffectiveSCR_EL3_NS, HaveSecureState,
    undefined_SecurityState, run_internal_pick, EL2, EL1, EL3]

theorem run_StatisticalProfilingEnabled {s : SState} (h : LinuxEL0Config s) :
    (StatisticalProfilingEnabled ()).run s = .ok false s := by
  obtain ⟨p, hp, he, _, _⟩ := h.pstate
  cfg_simp [StatisticalProfilingEnabled, StatisticalProfilingEnabled__1, run_readReg hp, he, HaveStatisticalProfiling,
    run_IsFeatureImplemented h, run_UsingAArch32 h, run_ProfilingBufferEnabled h, undefined_SecurityState,
    run_internal_pick]

theorem run_SPEBranch {s : SState} (h : LinuxEL0Config s) {N : Nat} (t : BitVec N) (bt : BranchType) (c tk : Bool) :
    (SPEBranch t bt c tk).run s =
      .ok () (if tk then s.set .SPESamplePreviousBranchAddressValid false else s) := by
  cases tk <;>
  cfg_simp [SPEBranch, SPEBranch__1, __IMPDEF_boolean, ImpDefBool, run_readReg h.pmsidr1,
    run_StatisticalProfilingEnabled h, IsZero, Sail.BitVec.length]

/-- The registers `BranchTo` may write (besides `_PC` and `__BranchTaken`, the BRBE/SPE bookkeeping). -/
def brRegs : List Register :=
  [.Branchtypetaken, .__last_branch_valid, .SPESamplePreviousBranchAddressValid, ._PC, .__BranchTaken]

theorem brRegs_not_cfg : ∀ r ∈ brRegs, r ∉ cfgRegs := by decide

set_option maxHeartbeats 4000000 in
theorem run_BranchTo {s : SState} (h : LinuxEL0Config s) (t : BitVec 64) (ht : t.toNat < 2 ^ 56)
    (bt : BranchType) (c : Bool) :
    ∃ s', (BranchTo t bt c).run s = .ok () s' ∧ s'.regs.get? ._PC = some t ∧
      s'.regs.get? .__BranchTaken = some true ∧ Touches s s' brRegs := by
  have t1 : Touches s (s.set .Branchtypetaken bt) brRegs := (Touches.refl s _).set _ _ (by decide)
  have h1 := h.of_touches t1 brRegs_not_cfg
  obtain ⟨p, hp, he, _, _⟩ := h1.pstate
  simp only [BranchTo, Hint_Branch, run_bind, run_writeReg, Sail.BitVec.length]
  cfg_simp [run_UsingAArch32 h1, run_readReg hp, he, Sail.BitVec.extractLsb]
  have ex : BitVec.extractLsb 63 0 t = t := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb_toNat]; omega
  rw [ex, run_AArch64_BranchAddr h1 t ht]
  simp only [HaveBRBExt, run_IsFeatureImplemented h1, HaveStatisticalProfiling]
  simp only [cfgFeat, num_of_Feature, cfgFeaturesOff]
  simp (config := { decide := true }) only [List.contains, List.elem, Int.reduceToNat, true_and, Bool.not_false]
  by_cases hb : ((bt == BranchType.BranchType_DIR) = true ∨ (bt == BranchType.BranchType_INDIR) = true ∨
      (bt == BranchType.BranchType_DIRCALL) = true ∨ (bt == BranchType.BranchType_INDCALL) = true ∨
      (bt == BranchType.BranchType_RET) = true)
  · have t2 : Touches s ((s.set .Branchtypetaken bt).set .__last_branch_valid false) brRegs := t1.set _ _ (by decide)
    have h2 := h.of_touches t2 brRegs_not_cfg
    rw [if_pos hb, run_BRBEBranch h1]
    simp only [run_pure, run_IsFeatureImplemented h2]
    simp (config := { decide := true }) only [cfgFeat, num_of_Feature, cfgFeaturesOff, List.contains, List.elem,
      Int.reduceToNat, Bool.not_false, ite_true]
    rw [run_SPEBranch h2]
    simp only [ite_true]
    refine ⟨_, rfl, by simp [get?_set_ne], by simp, ?_⟩
    exact ((t2.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)
  · rw [if_neg hb]
    simp only [run_pure, run_IsFeatureImplemented h1]
    simp (config := { decide := true }) only [cfgFeat, num_of_Feature, cfgFeaturesOff, List.contains, List.elem,
      Int.reduceToNat, Bool.not_false, ite_true]
    rw [run_SPEBranch h1]
    simp only [ite_true]
    refine ⟨_, rfl, by simp [get?_set_ne], by simp, ?_⟩
    exact ((t1.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem run_GCSPCRSelected {s : SState} (h : LinuxEL0Config s) : (GCSPCRSelected 0#2).run s = .ok false s := by
  unfold GCSPCRSelected
  simp only [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run]
  cfg_simp [run_readReg h.gcscre0, EL0, SailME.throw, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    ExceptT.run_bind, liftM, ExceptT.run_lift, MonadExceptOf.throw, ExceptT.run_throw, monadLift, MonadLift.monadLift]

theorem run_GCSPCREnabled {s : SState} (h : LinuxEL0Config s) : (GCSPCREnabled 0#2).run s = .ok false s := by
  cfg_simp [GCSPCREnabled, run_GCSPCRSelected h]

theorem gprVal_eq_of {s s' : SState} (hr : ∀ r, isGprReg r = true → s'.regs.get? r = s.regs.get? r) :
    ∀ i < 31, gprVal s' i = gprVal s i := by
  intro i hi
  match i, hi with
  | 0, _ => exact hr .R0 rfl
  | 1, _ => exact hr .R1 rfl
  | 2, _ => exact hr .R2 rfl
  | 3, _ => exact hr .R3 rfl
  | 4, _ => exact hr .R4 rfl
  | 5, _ => exact hr .R5 rfl
  | 6, _ => exact hr .R6 rfl
  | 7, _ => exact hr .R7 rfl
  | 8, _ => exact hr .R8 rfl
  | 9, _ => exact hr .R9 rfl
  | 10, _ => exact hr .R10 rfl
  | 11, _ => exact hr .R11 rfl
  | 12, _ => exact hr .R12 rfl
  | 13, _ => exact hr .R13 rfl
  | 14, _ => exact hr .R14 rfl
  | 15, _ => exact hr .R15 rfl
  | 16, _ => exact hr .R16 rfl
  | 17, _ => exact hr .R17 rfl
  | 18, _ => exact hr .R18 rfl
  | 19, _ => exact hr .R19 rfl
  | 20, _ => exact hr .R20 rfl
  | 21, _ => exact hr .R21 rfl
  | 22, _ => exact hr .R22 rfl
  | 23, _ => exact hr .R23 rfl
  | 24, _ => exact hr .R24 rfl
  | 25, _ => exact hr .R25 rfl
  | 26, _ => exact hr .R26 rfl
  | 27, _ => exact hr .R27 rfl
  | 28, _ => exact hr .R28 rfl
  | 29, _ => exact hr .R29 rfl
  | 30, _ => exact hr .R30 rfl
  | _ + 31, hi => exact absurd hi (by omega)

theorem Rel.touches {js : Janus.Arm64.State} {s s' : SState} {rs : List Register} (h : Rel js s)
    (ht : Touches s s' rs) (hd : ∀ r ∈ rs, isGprReg r = false ∧ r ≠ .SP_EL0 ∧ r ≠ .PSTATE) {t : BitVec 64}
    (hpc : s'.regs.get? ._PC = some t) : Rel { js with pc := t } s' where
  gpr i hi := by
    rw [gprVal_eq_of (fun r hr => ht r (fun hm => by have := (hd r hm).1; rw [hr] at this; cases this)) i hi]
    exact h.gpr i hi
  sp := by rw [ht _ (fun hm => (hd _ hm).2.1 rfl)]; exact h.sp
  pc := hpc
  pstate := by rw [ht _ (fun hm => (hd _ hm).2.2 rfl)]; exact h.pstate

/-! ## The executable check (`janus-asl-check` asserts `cfgOk` on its base state and every post-state) -/

/-- `LinuxEL0Config` as a `Bool` the check evaluates; `cfgOk_sound` connects the two. -/
def cfgOk (s : SState) : Bool :=
  (match s.regs.get? .FeatureImpl with
   | some v => (List.range 259).all fun i => v[i]! == !(cfgFeaturesOff.contains i)
   | none => false) &&
  s.regs.get? .SCR_EL3 == some 0x24006030401#64 && s.regs.get? .SCR == some 0#32 &&
  s.regs.get? .HCR_EL2 == some 0x30080000000#64 && s.regs.get? .HCRX_EL2 == some 0x800#64 &&
  s.regs.get? .TCR_EL1 == some 0x25b5903510#64 && s.regs.get? .MDCR_EL3 == some 0x10000000#64 &&
  s.regs.get? .MDCR_EL2 == some 0#64 && s.regs.get? .BRBFCR_EL1 == some 0#64 &&
  s.regs.get? .BRBCR_EL1 == some 0#64 && s.regs.get? .BRBCR_EL2 == some 0#64 &&
  s.regs.get? .PMSIDR_EL1 == some 0x103604f#64 && s.regs.get? .PMSCR_EL1 == some 0#64 &&
  s.regs.get? .PMSCR_EL2 == some 0#64 && s.regs.get? .PMBLIMITR_EL1 == some 0#64 &&
  s.regs.get? .PMBSR_EL1 == some 0#64 && s.regs.get? .GCSCRE0_EL1 == some 0#64 &&
  s.regs.get? .SPESampleInFlight == some false && s.regs.get? .InGuardedPage == some false &&
  s.regs.get? .SCTLR_EL1 == some 0x2000422fcf4f91d#64 &&
  s.regs.get? ._MPAM3_EL3 == some 0x4000000000000000#64 && s.regs.get? .MPAM2_EL2 == some 0#64 &&
  (match s.regs.get? .TSTATE with
   | some t => t.depth == 0
   | none => false) &&
  (match s.regs.get? .PSTATE with
   | some p => p.EL == 0#2 && p.nRW == 0#1 && p.SP == 0#1
   | none => false)

set_option maxRecDepth 100000 in
theorem num_of_Feature_range (f : Feature) : 0 ≤ num_of_Feature f ∧ (num_of_Feature f).toNat < 259 := by
  cases f <;> decide

theorem cfgOk_sound {s : SState} (h : cfgOk s = true) : LinuxEL0Config s := by
  simp only [cfgOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hf, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩,
    h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, hts⟩, hps⟩ := h
  refine ⟨?_, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, ?_, ?_⟩
  · split at hf
    · next v hv =>
      refine ⟨v, hv, fun f => ?_⟩
      obtain ⟨h0, hlt⟩ := num_of_Feature_range f
      have := List.all_eq_true.mp hf _ (List.mem_range.mpr hlt)
      simp only [beq_iff_eq] at this
      show v[(num_of_Feature f).toNat]! = cfgFeat f
      rw [this]; rfl
    · cases hf
  · split at hts
    · next tm htm => exact ⟨tm, htm, by simpa using hts⟩
    · cases hts
  · split at hps
    · next p hp =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hps
      exact ⟨p, hp, hps.1.1, hps.1.2, hps.2⟩
    · cases hps

end JanusASL.Proofs
