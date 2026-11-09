import JanusASL.Proofs.Examples
import JanusASL.Proofs.FP.Run

/-! # `Ensures.toASL_fp`: a Janus specification of a program with floating-point words holds of the ASL -/

namespace JanusASL.Proofs
open Janus Janus.Arm64 Janus.GoABI

/-- **A Janus specification holds of the ASL, floating point included.** As `Ensures.toASL`, for a program whose
words are all `FPStepOK` (integer, branch or scalar floating-point classes), from any ASL state related to the call
state under `Rel`, `FPRel`, `LinuxEL0Config` and `FPConfig`: the ASL run returns to the caller in a state related to
one satisfying the ABI and the postcondition, again under all four relations. -/
theorem Ensures.toASL_fp {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (hE : Ensures p entry args pre post)
    (hp : ∀ w ∈ p.segments.flatMap (·.words), FPStepOK w)
    (hcode : ∀ seg ∈ p.segments, seg.base + 4 * seg.words.length < 2 ^ 56)
    (hstub : ∀ st ∈ p.stubs, st.addr < 2 ^ 56)
    {ret : Nat} (hret : RetAddr p ret) {js : State} (hs : CallSetup (p.withExit ret) entry args js) (hpre : pre js)
    {s : SState} (h : Rel js s) (hf : FPRel js s) (hc : LinuxEL0Config s) (hfc : FPConfig s) :
    ∃ fuel s' js', aslRun (p.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ FPRel js' s' ∧ LinuxEL0Config s' ∧
      FPConfig s' ∧ ABIReturn js js' ∧ post js js' := by
  obtain ⟨fuel, js', hrun, hpost⟩ := hE ret hret js hs hpre
  have hp' : ∀ pc w, (p.withExit ret).fetch pc = some w → FPStepOK w := by
    intro pc w hf'
    obtain ⟨seg, hm, _, hw⟩ := fetchIn_some hf'
    exact hp w (List.mem_flatMap.mpr ⟨seg, hm, hw⟩)
  have hu : Untagged (p.withExit ret) := by
    refine ⟨by show ret < 2 ^ 56; have := hret.user; omega, fun pc w hf' => ?_, fun pc st hst => ?_⟩
    · obtain ⟨seg, hm, hlt, _⟩ := fetchIn_some hf'
      have := hcode seg hm; omega
    · have hm := List.mem_of_find?_eq_some hst
      have := List.find?_some hst
      simp only [decide_eq_true_eq] at this
      rw [← this]; exact hstub st hm
  have := run_agree_fp (p.withExit ret) hp' hu fuel js s _ h hf hc hfc hrun
  revert this
  cases hr : aslRun (p.withExit ret) fuel s with
  | returned s' => intro ⟨hrel, hfrel, hcf, hfcf⟩; exact ⟨fuel, s', js', hr, hrel, hfrel, hcf, hfcf, hpost⟩
  | stub _ _ _ => intro hf'; cases hf'
  | other => intro hf'; cases hf'

end JanusASL.Proofs
