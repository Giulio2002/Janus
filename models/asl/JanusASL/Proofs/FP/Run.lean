import JanusASL.Proofs.Run
import JanusASL.Proofs.FP.AgreeArith
import JanusASL.Proofs.FP.AgreeCcmp
import JanusASL.Proofs.FP.AgreeConv
import JanusASL.Proofs.FP.AgreeFcvtz
import JanusASL.Proofs.FP.AgreeFcvt
import JanusASL.Proofs.FP.FCmpCls

/-! # Whole runs with floating point: `FPStepOK` and `run_agree_fp`

`FPStepOK w` is `StepOK w` with the floating-point relation and configuration carried: from states
related under `Rel`, `FPRel`, `LinuxEL0Config` and `FPConfig`, whenever Janus steps `w` to a state
with an untagged PC, the ASL step completes with `Janus_OK` in states related the same way.
`run_agree_fp` is `run_agree` for programs all of whose words are `FPStepOK`. -/

namespace JanusASL.Proofs
open ArmASL ArmASL.Functions

def FPStepOK (w : Nat) : Prop :=
  ∀ (js js' : Janus.Arm64.State) (s : SState), Rel js s → FPRel js s → LinuxEL0Config s → FPConfig s →
    Janus.Arm64.step w js = .ok js' → js'.pc.toNat < 2 ^ 56 →
    ∃ s', (janus_step (BitVec.ofNat 32 w)).run s = .ok .Janus_OK s' ∧ Rel js' s' ∧ FPRel js' s' ∧
      LinuxEL0Config s' ∧ FPConfig s'

/-- What `run_agree_fp` concludes about an outcome. -/
def OutcomeRelFP : Janus.Outcome → AslOutcome → Prop
  | .returned js, .returned s => Rel js s ∧ FPRel js s ∧ LinuxEL0Config s ∧ FPConfig s
  | .stub n k js, .stub n' k' s => n = n' ∧ k = k' ∧ Rel js s ∧ FPRel js s ∧ LinuxEL0Config s ∧ FPConfig s
  | _, _ => False

theorem run_agree_fp (p : Janus.Program) (hp : ∀ pc w, p.fetch pc = some w → FPStepOK w) (hu : Untagged p) :
    ∀ (fuel : Nat) (js : Janus.Arm64.State) (s : SState) (o : Janus.Outcome), Rel js s → FPRel js s →
      LinuxEL0Config s → FPConfig s → p.run fuel js = .ok o → OutcomeRelFP o (aslRun p fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro js s o _ _ _ _ hr; simp [Janus.Program.run] at hr
  | succ fuel ih =>
    intro js s o h hf hc hfc hr
    simp only [Janus.Program.run] at hr
    simp only [aslRun, h.pc]
    by_cases he : js.pc.toNat = p.exitAddr
    · rw [if_pos he] at hr ⊢
      cases hr
      exact ⟨h, hf, hc, hfc⟩
    · rw [if_neg he] at hr ⊢
      cases hst : p.stubAt js.pc.toNat with
      | some st =>
        rw [hst] at hr; cases hr
        exact ⟨rfl, rfl, h, hf, hc, hfc⟩
      | none =>
        rw [hst] at hr
        cases hf' : p.fetch js.pc.toNat with
        | none => rw [hf'] at hr; cases hr
        | some w =>
          rw [hf'] at hr
          simp only [bind, Except.bind] at hr
          cases hs : Janus.Arm64.step w js with
          | error e => rw [hs] at hr; cases hr
          | ok js' =>
            rw [hs] at hr
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
                    cases hf'' : p.fetch js'.pc.toNat with
                    | none => rw [hf''] at hr; cases hr
                    | some w' => exact hu.2.1 _ _ hf''
            obtain ⟨s', hrun, hrel, hfrel, hcf, hfcf⟩ := hp _ _ hf' js js' s h hf hc hfc hs hnext
            simp only [hrun]
            exact ih js' s' o hrel hfrel hcf hfcf hr

/-! ## Every proved floating-point class is `FPStepOK` -/

section
variable {w : Nat} (hw : w < 2 ^ 32)
include hw

theorem fpStepOK_fcmp (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 16 = 8) (h14 : (w / 2 ^ 14) % 4 = 0) (h0 : w % 8 = 0)
    (hz : (w / 2 ^ 3) % 2 = 1 → (w / 2 ^ 16) % 32 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fcmp_agree hw htop hft h21 h10 h14 h0 hz h hf hc hfc hj

theorem fpStepOK_fmul (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fmul_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_fdiv (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 1) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fdiv_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_fadd (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 2) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fadd_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_fsub (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 4 = 2) (hop : (w / 2 ^ 12) % 16 = 3) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fsub_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_fmadd (htop : w / 2 ^ 24 = 0x1F) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fmadd_agree hw htop hft h21 h15 h hf hc hfc hj

theorem fpStepOK_fmsub (htop : w / 2 ^ 24 = 0x1F) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 0)
    (h15 : (w / 2 ^ 15) % 2 = 1) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fmsub_agree hw htop hft h21 h15 h hf hc hfc hj

theorem fpStepOK_fnmadd (htop : w / 2 ^ 24 = 0x1F) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h15 : (w / 2 ^ 15) % 2 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fnmadd_agree hw htop hft h21 h15 h hf hc hfc hj

theorem fpStepOK_fnmsub (htop : w / 2 ^ 24 = 0x1F) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h15 : (w / 2 ^ 15) % 2 = 1) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fnmsub_agree hw htop hft h21 h15 h hf hc hfc hj

theorem fpStepOK_fsqrt (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 32 = 16) (hop : (w / 2 ^ 15) % 64 = 3) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fsqrt_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_fccmp (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 4 = 1) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fccmp_agree hw htop hft h21 h10 h hf hc hfc hj

theorem fpStepOK_fcvt (htop : w / 2 ^ 24 = 0x1E) (hft : (w / 2 ^ 22) % 4 < 2) (h21 : (w / 2 ^ 21) % 2 = 1)
    (h10 : (w / 2 ^ 10) % 32 = 16)
    (hop : ((w / 2 ^ 15) % 64 = 4 ∧ (w / 2 ^ 22) % 4 = 1) ∨ ((w / 2 ^ 15) % 64 = 5 ∧ (w / 2 ^ 22) % 4 = 0)) :
    FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fcvt_agree hw htop hft h21 h10 hop h hf hc hfc hj

theorem fpStepOK_scvtf (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0) (hop : (w / 2 ^ 16) % 8 = 2)
    (hrm : (w / 2 ^ 19) % 4 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => scvtf_agree hw htop hft h21 h10 hop hrm h hf hc hfc hj

theorem fpStepOK_ucvtf (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0) (hop : (w / 2 ^ 16) % 8 = 3)
    (hrm : (w / 2 ^ 19) % 4 = 0) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => ucvtf_agree hw htop hft h21 h10 hop hrm h hf hc hfc hj

theorem fpStepOK_fcvtzs (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0) (hop : (w / 2 ^ 16) % 8 = 0)
    (hrm : (w / 2 ^ 19) % 4 = 3) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fcvtzs_agree hw htop hft h21 h10 hop hrm h hf hc hfc hj

theorem fpStepOK_fcvtzu (htop : w / 2 ^ 24 = 0x1E ∨ w / 2 ^ 24 = 0x9E) (hft : (w / 2 ^ 22) % 4 < 2)
    (h21 : (w / 2 ^ 21) % 2 = 1) (h10 : (w / 2 ^ 10) % 64 = 0) (hop : (w / 2 ^ 16) % 8 = 1)
    (hrm : (w / 2 ^ 19) % 4 = 3) : FPStepOK w :=
  fun _ _ _ h hf hc hfc hj _ => fcvtzu_agree hw htop hft h21 h10 hop hrm h hf hc hfc hj

end

end JanusASL.Proofs
