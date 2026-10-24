import JanusASL.Proofs.Run
import Janus

/-! # Transferring shipped example theorems to the ASL

`Ensures.toASL` turns a Janus `Ensures` specification of a program whose words are all in the
proved subset into the same statement about the ASL run (`aslRun`), for every ASL state related to
the call state under `LinuxEL0Config`. `janus verify --asl` applies it to a verified theorem about
the identity-checked `Extracted.program` (JanusASL/JanusASL/Verify.lean, docs/ASL.md); the shipped
examples Add, Max, Mul64 and Add128 are transferred that way, from their artifacts
(`cmd/janus` test `TestASLExamples`, `.github/workflows/asl.yml`). -/

namespace JanusASL.Proofs
open Janus Janus.Arm64 Janus.GoABI

theorem fetchIn_some {segs : List Segment} {pc w : Nat} (h : Program.fetchIn segs pc = some w) :
    ∃ seg ∈ segs, pc < seg.base + 4 * seg.words.length ∧ w ∈ seg.words := by
  induction segs with
  | nil => simp [Program.fetchIn] at h
  | cons seg rest ih =>
    simp only [Program.fetchIn] at h
    split at h
    · next hb =>
      split at h
      · next w' hw =>
        cases h
        refine ⟨seg, List.mem_cons_self .., ?_, List.mem_of_getElem? hw⟩
        have := (List.getElem?_eq_some_iff.mp hw).1
        omega
      · obtain ⟨sg, hm, h1, h2⟩ := ih h
        exact ⟨sg, List.mem_cons_of_mem _ hm, h1, h2⟩
    · obtain ⟨sg, hm, h1, h2⟩ := ih h
      exact ⟨sg, List.mem_cons_of_mem _ hm, h1, h2⟩

/-- **A Janus specification holds of the ASL.** If every word of `p` is in the proved subset,
its code is untagged and it has no stubs below the tag boundary issue (`hu`), then every Janus
`Ensures` theorem about `p` gives: from any ASL state related to a call state (under
`LinuxEL0Config`), the ASL run returns to the caller in a state related to one satisfying the
postcondition. -/
theorem Ensures.toASL {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (hE : Ensures p entry args pre post)
    (hp : ∀ w ∈ p.segments.flatMap (·.words), StepOK w)
    (hcode : ∀ seg ∈ p.segments, seg.base + 4 * seg.words.length < 2 ^ 56)
    (hstub : ∀ st ∈ p.stubs, st.addr < 2 ^ 56)
    {ret : Nat} (hret : RetAddr p ret) {js : State} (hs : CallSetup (p.withExit ret) entry args js) (hpre : pre js)
    {s : SState} (h : Rel js s) (hc : LinuxEL0Config s) :
    ∃ fuel s' js', aslRun (p.withExit ret) fuel s = .returned s' ∧ Rel js' s' ∧ LinuxEL0Config s' ∧
      ABIReturn js js' ∧ post js js' := by
  obtain ⟨fuel, js', hrun, hpost⟩ := hE ret hret js hs hpre
  have hp' : ∀ pc w, (p.withExit ret).fetch pc = some w → StepOK w := by
    intro pc w hf
    obtain ⟨seg, hm, _, hw⟩ := fetchIn_some hf
    exact hp w (List.mem_flatMap.mpr ⟨seg, hm, hw⟩)
  have hu : Untagged (p.withExit ret) := by
    refine ⟨by show ret < 2 ^ 56; have := hret.user; omega, fun pc w hf => ?_, fun pc st hst => ?_⟩
    · obtain ⟨seg, hm, hlt, _⟩ := fetchIn_some hf
      have := hcode seg hm; omega
    · have hm := List.mem_of_find?_eq_some hst
      have := List.find?_some hst
      simp only [decide_eq_true_eq] at this
      rw [← this]; exact hstub st hm
  have := run_agree (p.withExit ret) hp' hu fuel js s _ h hc hrun
  revert this
  cases hr : aslRun (p.withExit ret) fuel s with
  | returned s' => intro ⟨hrel, hcf⟩; exact ⟨fuel, s', js', hr, hrel, hcf, hpost⟩
  | stub _ _ _ => intro hf; cases hf
  | other => intro hf; cases hf

end JanusASL.Proofs
