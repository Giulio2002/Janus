import JanusASL.Proofs.Rel

/-! # `LinuxEL0Config`, the predicate (the evaluation lemmas are in Config.lean)

See Config.lean and docs/ASL.md. Defined here, below Step.lean, so that every class theorem can
conclude that its step preserves the configuration. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- Features off in the check's configuration (indices of `num_of_Feature`). -/
def cfgFeaturesOff : List Nat := [1, 2, 3, 18, 19, 87, 88, 95, 96, 258]


/-- A feature's value in the configuration. -/
def cfgFeat (f : Feature) : Bool := !(cfgFeaturesOff.contains (num_of_Feature f).toNat)

structure LinuxEL0Config (s : SState) : Prop where
  fi : ∃ v : Vector Bool 259, s.regs.get? .FeatureImpl = some v ∧ ∀ f : Feature, v[num_of_Feature f]! = cfgFeat f
  scr3 : s.regs.get? .SCR_EL3 = some 0x24006030401#64
  scr : s.regs.get? .SCR = some 0#32
  hcr2 : s.regs.get? .HCR_EL2 = some 0x30080000000#64
  hcrx2 : s.regs.get? .HCRX_EL2 = some 0x800#64
  tcr1 : s.regs.get? .TCR_EL1 = some 0x25b5903510#64
  mdcr3 : s.regs.get? .MDCR_EL3 = some 0x10000000#64
  mdcr2 : s.regs.get? .MDCR_EL2 = some 0#64
  brbfcr1 : s.regs.get? .BRBFCR_EL1 = some 0#64
  brbcr1 : s.regs.get? .BRBCR_EL1 = some 0#64
  brbcr2 : s.regs.get? .BRBCR_EL2 = some 0#64
  pmsidr1 : s.regs.get? .PMSIDR_EL1 = some 0x103604f#64
  pmscr1 : s.regs.get? .PMSCR_EL1 = some 0#64
  pmscr2 : s.regs.get? .PMSCR_EL2 = some 0#64
  pmblimitr1 : s.regs.get? .PMBLIMITR_EL1 = some 0#64
  pmbsr1 : s.regs.get? .PMBSR_EL1 = some 0#64
  gcscre0 : s.regs.get? .GCSCRE0_EL1 = some 0#64
  speInFlight : s.regs.get? .SPESampleInFlight = some false
  inGuarded : s.regs.get? .InGuardedPage = some false
  sctlr1 : s.regs.get? .SCTLR_EL1 = some 0x2000422fcf4f91d#64
  mpam3 : s.regs.get? ._MPAM3_EL3 = some 0x4000000000000000#64
  mpam2 : s.regs.get? .MPAM2_EL2 = some 0#64
  tstate : ∃ t : TMState, s.regs.get? .TSTATE = some t ∧ t.depth = 0
  pstate : ∃ p : ProcState, s.regs.get? .PSTATE = some p ∧ p.EL = 0#2 ∧ p.nRW = 0#1 ∧ p.SP = 0#1

/-- `s'` differs from `s` at most in the registers `rs`. -/
def Touches (s s' : SState) (rs : List Register) : Prop := ∀ r, r ∉ rs → s'.regs.get? r = s.regs.get? r

theorem Touches.refl (s : SState) (rs : List Register) : Touches s s rs := fun _ _ => rfl

theorem Touches.set {s s' : SState} {rs : List Register} (h : Touches s s' rs) (r : Register) (v : RegisterType r)
    (hr : r ∈ rs) : Touches s (s'.set r v) rs := by
  intro x hx
  rw [get?_set_ne _ _ (by rintro rfl; exact hx hr)]
  exact h x hx

/-- The configuration registers. -/
def cfgRegs : List Register :=
  [.FeatureImpl, .SCR_EL3, .SCR, .HCR_EL2, .HCRX_EL2, .TCR_EL1, .MDCR_EL3, .MDCR_EL2, .BRBFCR_EL1, .BRBCR_EL1,
   .BRBCR_EL2, .PMSIDR_EL1, .PMSCR_EL1, .PMSCR_EL2, .PMBLIMITR_EL1, .PMBSR_EL1, .GCSCRE0_EL1, .SPESampleInFlight,
   .InGuardedPage, .SCTLR_EL1, ._MPAM3_EL3, .MPAM2_EL2, .TSTATE, .PSTATE]

theorem LinuxEL0Config.of_eq {s s' : SState} (h : LinuxEL0Config s)
    (e : ∀ r ∈ cfgRegs, s'.regs.get? r = s.regs.get? r) : LinuxEL0Config s' := by
  obtain ⟨v, hv, hf⟩ := h.fi
  obtain ⟨p, hp, hpe⟩ := h.pstate
  obtain ⟨tm, htm, htd⟩ := h.tstate
  exact {
    fi := ⟨v, by rw [e _ (by decide)]; exact hv, hf⟩
    scr3 := by rw [e _ (by decide)]; exact h.scr3
    scr := by rw [e _ (by decide)]; exact h.scr
    hcr2 := by rw [e _ (by decide)]; exact h.hcr2
    hcrx2 := by rw [e _ (by decide)]; exact h.hcrx2
    tcr1 := by rw [e _ (by decide)]; exact h.tcr1
    mdcr3 := by rw [e _ (by decide)]; exact h.mdcr3
    mdcr2 := by rw [e _ (by decide)]; exact h.mdcr2
    brbfcr1 := by rw [e _ (by decide)]; exact h.brbfcr1
    brbcr1 := by rw [e _ (by decide)]; exact h.brbcr1
    brbcr2 := by rw [e _ (by decide)]; exact h.brbcr2
    pmsidr1 := by rw [e _ (by decide)]; exact h.pmsidr1
    pmscr1 := by rw [e _ (by decide)]; exact h.pmscr1
    pmscr2 := by rw [e _ (by decide)]; exact h.pmscr2
    pmblimitr1 := by rw [e _ (by decide)]; exact h.pmblimitr1
    pmbsr1 := by rw [e _ (by decide)]; exact h.pmbsr1
    gcscre0 := by rw [e _ (by decide)]; exact h.gcscre0
    speInFlight := by rw [e _ (by decide)]; exact h.speInFlight
    inGuarded := by rw [e _ (by decide)]; exact h.inGuarded
    sctlr1 := by rw [e _ (by decide)]; exact h.sctlr1
    mpam3 := by rw [e _ (by decide)]; exact h.mpam3
    mpam2 := by rw [e _ (by decide)]; exact h.mpam2
    tstate := ⟨tm, by rw [e _ (by decide)]; exact htm, htd⟩
    pstate := ⟨p, by rw [e _ (by decide)]; exact hp, hpe⟩ }

theorem LinuxEL0Config.of_touches {s s' : SState} {rs : List Register} (h : LinuxEL0Config s) (ht : Touches s s' rs)
    (hd : ∀ r ∈ rs, r ∉ cfgRegs) : LinuxEL0Config s' :=
  h.of_eq fun r hr => ht r (fun hm => hd r hm hr)

theorem cfgRegs_not_gpr : ∀ r ∈ cfgRegs, isGprReg r = false := by decide

theorem LinuxEL0Config.setGpr {s : SState} (h : LinuxEL0Config s) (v : BitVec 64) {d : Nat} (hd : d < 31) :
    LinuxEL0Config (setGpr s v d) :=
  h.of_eq fun r hr => get?_setGpr s v hd r (cfgRegs_not_gpr r hr)


/-- A step changed no configuration register other than (possibly) PSTATE. -/
def CfgFrame (s s' : SState) : Prop := ∀ r ∈ cfgRegs, r ≠ .PSTATE → s'.regs.get? r = s.regs.get? r

theorem LinuxEL0Config.of_frame {s s' : SState} (h : LinuxEL0Config s) (hf : CfgFrame s s')
    (hp : ∃ p : ProcState, s'.regs.get? .PSTATE = some p ∧ p.EL = 0#2 ∧ p.nRW = 0#1 ∧ p.SP = 0#1) :
    LinuxEL0Config s' := by
  obtain ⟨v, hv, hfe⟩ := h.fi
  obtain ⟨tm, htm, htd⟩ := h.tstate
  exact {
    fi := ⟨v, by rw [hf _ (by decide) (by decide)]; exact hv, hfe⟩
    scr3 := by rw [hf _ (by decide) (by decide)]; exact h.scr3
    scr := by rw [hf _ (by decide) (by decide)]; exact h.scr
    hcr2 := by rw [hf _ (by decide) (by decide)]; exact h.hcr2
    hcrx2 := by rw [hf _ (by decide) (by decide)]; exact h.hcrx2
    tcr1 := by rw [hf _ (by decide) (by decide)]; exact h.tcr1
    mdcr3 := by rw [hf _ (by decide) (by decide)]; exact h.mdcr3
    mdcr2 := by rw [hf _ (by decide) (by decide)]; exact h.mdcr2
    brbfcr1 := by rw [hf _ (by decide) (by decide)]; exact h.brbfcr1
    brbcr1 := by rw [hf _ (by decide) (by decide)]; exact h.brbcr1
    brbcr2 := by rw [hf _ (by decide) (by decide)]; exact h.brbcr2
    pmsidr1 := by rw [hf _ (by decide) (by decide)]; exact h.pmsidr1
    pmscr1 := by rw [hf _ (by decide) (by decide)]; exact h.pmscr1
    pmscr2 := by rw [hf _ (by decide) (by decide)]; exact h.pmscr2
    pmblimitr1 := by rw [hf _ (by decide) (by decide)]; exact h.pmblimitr1
    pmbsr1 := by rw [hf _ (by decide) (by decide)]; exact h.pmbsr1
    gcscre0 := by rw [hf _ (by decide) (by decide)]; exact h.gcscre0
    speInFlight := by rw [hf _ (by decide) (by decide)]; exact h.speInFlight
    inGuarded := by rw [hf _ (by decide) (by decide)]; exact h.inGuarded
    sctlr1 := by rw [hf _ (by decide) (by decide)]; exact h.sctlr1
    mpam3 := by rw [hf _ (by decide) (by decide)]; exact h.mpam3
    mpam2 := by rw [hf _ (by decide) (by decide)]; exact h.mpam2
    tstate := ⟨tm, by rw [hf _ (by decide) (by decide)]; exact htm, htd⟩
    pstate := hp }

end JanusASL.Proofs
