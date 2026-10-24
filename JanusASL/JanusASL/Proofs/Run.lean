import JanusASL.Proofs.Branch
import JanusASL.Proofs.AddSubImmClass
import JanusASL.Proofs.AddSubCarry
import JanusASL.Proofs.CondSel
import JanusASL.Proofs.CondCmp
import JanusASL.Proofs.Madd
import JanusASL.Proofs.AddSubShifted
import JanusASL.Proofs.LogicalShifted
import JanusASL.Proofs.ShiftV
import JanusASL.Proofs.MoveWide
import JanusASL.Proofs.Maddl
import JanusASL.Proofs.Mulh
import JanusASL.Proofs.Div
import JanusASL.Proofs.LogicalImm
import JanusASL.Proofs.Bitfield
import JanusASL.Proofs.Extr
import JanusASL.Proofs.PcRel
import JanusASL.Proofs.AddSubExt
import JanusASL.Proofs.DP1
import JanusASL.Proofs.Rev

/-! # Whole runs: Janus' `Program.run` against iterated ASL steps

`StepOK w` is the per-word statement every proved class gives (`stepOK_*`): from related states
under `LinuxEL0Config`, whenever Janus steps `w` to a state with an untagged PC, the ASL step
completes with `Janus_OK` in a related state that is again `LinuxEL0Config`. `aslRun` iterates
the generated ASL step (`janus_step`) on the words the program's own `fetch` returns at the
ASL's `_PC`, ending, like `Program.run`, at the exit address or a stub. `run_agree`: for a
program all of whose words are `StepOK` and whose code, stubs and exit address are untagged,
every run of Janus that returns or reaches a stub is matched by the ASL run, with related final
states. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

/-- The per-word agreement every proved class gives. -/
def StepOK (w : Nat) : Prop :=
  ∀ (js js' : Janus.Arm64.State) (s : SState), Rel js s → LinuxEL0Config s →
    Janus.Arm64.step w js = .ok js' → js'.pc.toNat < 2 ^ 56 →
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ LinuxEL0Config s'

theorem StepOK.of_agree {w : Nat}
    (H : ∀ (js : Janus.Arm64.State) (s : SState), Rel js s → ∃ js' s', Janus.Arm64.step w js = .ok js' ∧
      (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧
      (LinuxEL0Config s → LinuxEL0Config s')) : StepOK w := by
  intro js js' s h hc hst _
  obtain ⟨js'', s', h1, h2, h3, h4⟩ := H js s h
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h4 hc⟩

theorem StepOK.of_agree_cfg {w : Nat}
    (H : ∀ (js : Janus.Arm64.State) (s : SState), Rel js s → LinuxEL0Config s → ∃ js' s',
      Janus.Arm64.step w js = .ok js' ∧ (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧
      Rel js' s' ∧ (LinuxEL0Config s → LinuxEL0Config s')) : StepOK w := by
  intro js js' s h hc hst _
  obtain ⟨js'', s', h1, h2, h3, h4⟩ := H js s h hc
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h4 hc⟩

/-! ## The ASL run -/

inductive AslOutcome where
  | returned (s : SState)
  | stub (name : String) (kind : Janus.StubKind) (s : SState)
  /-- Anything else: out of fuel, no code at the PC, an ASL step not `Janus_OK`. -/
  | other

def aslRun (p : Janus.Program) : Nat → SState → AslOutcome
  | 0, _ => .other
  | fuel + 1, s =>
    match s.regs.get? ._PC with
    | none => .other
    | some pc =>
      if pc.toNat = p.exitAddr then .returned s else
      match p.stubAt pc.toNat with
      | some st => .stub st.name st.kind s
      | none =>
        match p.fetch pc.toNat with
        | none => .other
        | some w =>
          match (janus_step (BitVec.ofNat 32 w)).run s with
          | .ok .Janus_OK s' => aslRun p fuel s'
          | _ => .other

/-- The program's code, stubs and exit address are untagged (below `2^56`). -/
def Untagged (p : Janus.Program) : Prop :=
  p.exitAddr < 2 ^ 56 ∧ (∀ pc w, p.fetch pc = some w → pc < 2 ^ 56) ∧ (∀ pc st, p.stubAt pc = some st → pc < 2 ^ 56)

/-- What `run_agree` concludes about an outcome. -/
def OutcomeRel : Janus.Outcome → AslOutcome → Prop
  | .returned js, .returned s => Rel js s ∧ LinuxEL0Config s
  | .stub n k js, .stub n' k' s => n = n' ∧ k = k' ∧ Rel js s ∧ LinuxEL0Config s
  | _, _ => False

/-- **Runs agree.** For a program whose every word is in the proved subset (`StepOK`) and whose
addresses are untagged: if Janus' `run` returns (`.ok (.returned js')`) or reaches a stub
(`.ok (.stub ..)`), the ASL run with the same fuel, from any related `LinuxEL0Config` state, ends
the same way in a related state. Janus faults (`.error`) are not covered: there Janus is
conservative and the ASL may continue. -/
theorem run_agree (p : Janus.Program) (hp : ∀ pc w, p.fetch pc = some w → StepOK w) (hu : Untagged p) :
    ∀ (fuel : Nat) (js : Janus.Arm64.State) (s : SState) (o : Janus.Outcome), Rel js s → LinuxEL0Config s →
      p.run fuel js = .ok o → OutcomeRel o (aslRun p fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro js s o _ _ hr; simp [Janus.Program.run] at hr
  | succ fuel ih =>
    intro js s o h hc hr
    simp only [Janus.Program.run] at hr
    simp only [aslRun, h.pc]
    by_cases he : js.pc.toNat = p.exitAddr
    · rw [if_pos he] at hr ⊢
      cases hr
      exact ⟨h, hc⟩
    · rw [if_neg he] at hr ⊢
      cases hst : p.stubAt js.pc.toNat with
      | some st =>
        rw [hst] at hr; cases hr
        exact ⟨rfl, rfl, h, hc⟩
      | none =>
        rw [hst] at hr
        cases hf : p.fetch js.pc.toNat with
        | none => rw [hf] at hr; cases hr
        | some w =>
          rw [hf] at hr
          simp only [bind, Except.bind] at hr
          cases hs : Janus.Arm64.step w js with
          | error e => rw [hs] at hr; cases hr
          | ok js' =>
            rw [hs] at hr
            -- the next PC is untagged: the run continues from it and returns or stops at a stub
            have hnext : js'.pc.toNat < 2 ^ 56 := by
              cases fuel with
              | zero => simp [Janus.Program.run] at hr
              | succ f =>
                simp only [Janus.Program.run] at hr
                by_cases he' : js'.pc.toNat = p.exitAddr
                · rw [he']; exact hu.1
                · rw [if_neg he'] at hr
                  cases hst' : p.stubAt js'.pc.toNat with
                  | some st => exact hu.2.2 _ _ hst'
                  | none =>
                    rw [hst'] at hr
                    cases hf' : p.fetch js'.pc.toNat with
                    | none => rw [hf'] at hr; cases hr
                    | some w' => exact hu.2.1 _ _ hf'
            obtain ⟨s', hrun, hrel, hcf⟩ := hp _ _ hf js js' s h hc hs hnext
            simp only [hrun]
            exact ih js' s' o hrel hcf hr

/-! ## Every proved class is `StepOK` -/

section
variable {w : Nat} (hw : w < 2 ^ 32)
include hw

theorem stepOK_addSubImm (hc : (w / 2 ^ 23) % 64 = 0b100010) : StepOK w :=
  StepOK.of_agree fun _ _ h => addSubImm_agree hw hc h
theorem stepOK_addSubShifted (h1 : (w / 2 ^ 24) % 32 = 0b01011) (h2 : (w / 2 ^ 21) % 2 = 0)
    (h3 : (w / 2 ^ 22) % 4 ≠ 3) (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : StepOK w :=
  StepOK.of_agree fun _ _ h => addSubShifted_agree hw h1 h2 h3 h4 h
theorem stepOK_addSubExt (h1 : (w / 2 ^ 24) % 32 = 0b01011) (h2 : (w / 2 ^ 21) % 8 = 1)
    (h3 : (w / 2 ^ 10) % 8 ≤ 4) : StepOK w :=
  StepOK.of_agree fun _ _ h => addSubExt_agree hw h1 h2 h3 h
theorem stepOK_addSubCarry (h1 : (w / 2 ^ 21) % 256 = 0b11010000) (h2 : (w / 2 ^ 10) % 64 = 0) : StepOK w :=
  StepOK.of_agree fun _ _ h => addSubCarry_agree hw h1 h2 h
theorem stepOK_logicalShifted (h1 : (w / 2 ^ 24) % 32 = 0b01010)
    (h4 : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : StepOK w :=
  StepOK.of_agree fun _ _ h => logicalShifted_agree hw h1 h4 h
theorem stepOK_logicalImm (hc : (w / 2 ^ 23) % 64 = 0b100100) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0)
    (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      true (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true) : StepOK w :=
  StepOK.of_agree fun _ _ h => logicalImm_agree hw hc hsf hdbm h
theorem stepOK_moveWide (hc : (w / 2 ^ 23) % 64 = 0b100101) (hop : (w / 2 ^ 29) % 4 ≠ 1)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 22) % 2 = 0) : StepOK w :=
  StepOK.of_agree fun _ _ h => moveWide_agree hw hc hop hsf h
theorem stepOK_bitfield (hc : (w / 2 ^ 23) % 64 = 0b100110) (hop : (w / 2 ^ 29) % 4 ≠ 3)
    (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2)
    (hsf : (w / 2 ^ 31) % 2 = 1 ∨ ((w / 2 ^ 16) % 64 < 32 ∧ (w / 2 ^ 10) % 64 < 32))
    (hdbm : (Janus.Arm64.decodeBitMasks (Janus.Arm64.bit w 22) (Janus.Arm64.bits w 15 10) (Janus.Arm64.bits w 21 16)
      false (if Janus.Arm64.bit w 31 then 64 else 32)).isSome = true) : StepOK w :=
  StepOK.of_agree fun _ _ h => bitfield_agree hw hc hop hN hsf hdbm h
theorem stepOK_extr (hc : (w / 2 ^ 23) % 64 = 0b100111) (h0 : (w / 2 ^ 29) % 4 = 0) (h21 : (w / 2 ^ 21) % 2 = 0)
    (hN : (w / 2 ^ 31) % 2 = (w / 2 ^ 22) % 2) (hsf : (w / 2 ^ 31) % 2 = 1 ∨ (w / 2 ^ 10) % 64 < 32) : StepOK w :=
  StepOK.of_agree fun _ _ h => extr_agree hw hc h0 h21 hN hsf h
theorem stepOK_pcrel (hc : (w / 2 ^ 24) % 32 = 0b10000) : StepOK w :=
  StepOK.of_agree fun _ _ h => pcrel_agree hw hc h
theorem stepOK_condSel (h1 : (w / 2 ^ 21) % 512 = 0b011010100) (h2 : (w / 2 ^ 11) % 2 = 0) : StepOK w :=
  StepOK.of_agree_cfg fun _ _ h hc => condSel_agree hw h1 h2 h hc.speInFlight
theorem stepOK_condCmpReg (h1 : (w / 2 ^ 21) % 512 = 0b111010010) (h2 : (w / 2 ^ 10) % 2 = 0)
    (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 0) : StepOK w :=
  StepOK.of_agree_cfg fun _ _ h hc => condCmpReg_agree hw h1 h2 h3 h4 h hc.speInFlight
theorem stepOK_condCmpImm (h1 : (w / 2 ^ 21) % 512 = 0b111010010) (h2 : (w / 2 ^ 10) % 2 = 0)
    (h3 : (w / 2 ^ 4) % 2 = 0) (h4 : (w / 2 ^ 11) % 2 = 1) : StepOK w :=
  StepOK.of_agree_cfg fun _ _ h hc => condCmpImm_agree hw h1 h2 h3 h4 h hc.speInFlight
theorem stepOK_madd (h1 : (w / 2 ^ 21) % 1024 = 0b0011011000) : StepOK w :=
  StepOK.of_agree fun _ _ h => madd_agree hw h1 h
theorem stepOK_maddl (hc : (w / 2 ^ 24) % 256 = 0b10011011) (h2 : (w / 2 ^ 21) % 4 = 1) : StepOK w :=
  StepOK.of_agree fun _ _ h => maddl_agree hw hc h2 h
theorem stepOK_mulh (hc : (w / 2 ^ 24) % 256 = 0b10011011) (h2 : (w / 2 ^ 21) % 4 = 2) (h3 : (w / 2 ^ 15) % 2 = 0)
    (h4 : (w / 2 ^ 10) % 32 = 31) : StepOK w :=
  StepOK.of_agree fun _ _ h => mulh_agree hw hc h2 h3 h4 h
theorem stepOK_div (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110) (h2 : (w / 2 ^ 11) % 32 = 1) : StepOK w :=
  StepOK.of_agree fun _ _ h => div_agree hw h1 h2 h
theorem stepOK_shiftV (h1 : (w / 2 ^ 21) % 1024 = 0b0011010110) (h2 : (w / 2 ^ 12) % 16 = 0b0010) : StepOK w :=
  StepOK.of_agree fun _ _ h => shiftV_agree hw h1 h2 h
theorem stepOK_rbit (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 0) : StepOK w :=
  StepOK.of_agree fun _ _ h => rbit_agree hw h1 h2 h3 h
theorem stepOK_clz (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 4) : StepOK w :=
  StepOK.of_agree fun _ _ h => clz_agree hw h1 h2 h3 h
theorem stepOK_cls (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 5) : StepOK w :=
  StepOK.of_agree fun _ _ h => cls_agree hw h1 h2 h3 h
theorem stepOK_rev16 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 1) : StepOK w :=
  StepOK.of_agree fun _ _ h => rev16_agree hw h1 h2 h3 h
theorem stepOK_rev32 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 2) : StepOK w :=
  StepOK.of_agree fun _ _ h => rev32_agree hw h1 h2 h3 h
theorem stepOK_rev64 (h1 : (w / 2 ^ 21) % 1024 = 0b1011010110) (h2 : (w / 2 ^ 16) % 32 = 0)
    (h3 : (w / 2 ^ 10) % 64 = 3) (hsf : (w / 2 ^ 31) % 2 = 1) : StepOK w :=
  StepOK.of_agree fun _ _ h => rev64_agree hw h1 h2 h3 hsf h

theorem stepOK_b (hc : (w / 2 ^ 26) % 32 = 0b00101) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_b_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  have hpc' : js'.pc = js.pc + Janus.Arm64.sext64 28 (Janus.Arm64.bits w 25 0 * 4) := by
    cases hst'; split <;> rfl
  obtain ⟨js'', s', h1, h2, h3, h4⟩ := b_agree hw hc h hcfg (hpc' ▸ hpc)
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h4⟩

theorem stepOK_bcond (hc : (w / 2 ^ 24) % 256 = 0b01010100) (h4 : (w / 2 ^ 4) % 2 = 0) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_bcond_class hw hc h4)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  have ht : Janus.Arm64.conditionHolds (Janus.Arm64.bits w 3 0) js.flags = true →
      (js.pc + Janus.Arm64.sext64 21 (Janus.Arm64.bits w 23 5 * 4)).toNat < 2 ^ 56 := by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc
  obtain ⟨js'', s', h1, h2, h3, h5⟩ := bcond_agree hw hc h4 h hcfg ht
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h5⟩

theorem stepOK_cb (hc : (w / 2 ^ 25) % 64 = 0b011010) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_cb_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  obtain ⟨js'', s', h1, h2, h3, h5⟩ := cb_agree hw hc h hcfg (by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc)
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h5⟩

theorem stepOK_tb (hc : (w / 2 ^ 25) % 64 = 0b011011) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_tb_class hw hc)] at hst'
  simp only [Janus.Arm64.exec] at hst'
  obtain ⟨js'', s', h1, h2, h3, h5⟩ := tb_agree hw hc h hcfg (by
    intro hcnd; rw [if_pos hcnd] at hst'; cases hst'; exact hpc)
  rw [hst] at h1; cases h1
  exact ⟨s', h2, h3, h5⟩

theorem stepOK_br (h0 : (w / 2 ^ 10) % 4194304 = 3508160) (h1 : w % 32 = 0) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_br_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5⟩ := br_agree hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  exact ⟨s', h3, h4, h5⟩

theorem stepOK_blr (h0 : (w / 2 ^ 10) % 4194304 = 3510208) (h1 : w % 32 = 0) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_blr_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5⟩ := blr_agree hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  exact ⟨s', h3, h4, h5⟩

theorem stepOK_ret (h0 : (w / 2 ^ 10) % 4194304 = 3512256) (h1 : w % 32 = 0) : StepOK w := by
  intro js js' s h hcfg hst hpc
  have hst' := hst
  rw [Janus.Arm64.step_of_decode (decode_ret_class hw h0 h1)] at hst'
  simp only [Janus.Arm64.exec, Janus.Arm64.branchReg] at hst'
  have ht : ¬ (js.readZR (Janus.Arm64.bits w 9 5)).toNat ≥ 2 ^ 56 := by
    intro hge; rw [if_pos hge] at hst'; cases hst'
  rw [if_neg ht] at hst'
  have hal : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0 := by
    by_cases hne : (js.readZR (Janus.Arm64.bits w 9 5)).toNat % 4 = 0
    · exact hne
    · rw [if_neg hne] at hst'; cases hst'
  obtain ⟨js'', s', h2, h3, h4, h5⟩ := ret_agree hw h0 h1 h hcfg (by omega) hal
  rw [hst] at h2; cases h2
  exact ⟨s', h3, h4, h5⟩

end

end JanusASL.Proofs
