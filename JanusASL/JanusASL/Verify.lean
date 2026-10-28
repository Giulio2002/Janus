import JanusASL.Classify
import JanusASL.Proofs.Run
import JanusASL.Proofs.FP.Run
import JanusASL.Proofs.FP.IntLift
import JanusASL.Proofs.Examples
import Janus.Tools.Audit

/-! # `janus verify --asl`: the ASL corollary of a verified Janus theorem

`janus verify <outdir> --asl` compiles, next to the user's proof, two modules it writes itself:

* `JanusASLWords` (trusted: it imports only `Extracted` and `JanusASL.Classify`) proves
  `JanusASL.Classify.covered Extracted.program = true` by kernel evaluation (`decide +kernel`):
  every word of the identity-checked program is in the proved subset;
* `JanusASLCorollary` imports the proof and `JanusASLWords`, and runs
  `janus_asl_corollary JanusASLCorollary.correctness_asl of <thm> using JanusASLWords.covered`,
  which adds the theorem `JanusAudit.aslCorollary` derives: `Ensures.toASL` applied to the user's
  theorem, with the three facts about the program discharged by `covered_sound`.

The trusted auditor (`JanusAudit.runASL`) then re-derives the type with the same function and
checks the corollary has exactly that type. See docs/ASL.md. -/

namespace JanusASL.Verify
open Janus JanusASL.Classify JanusASL.Proofs

theorem ite_some {P : Prop} [Decidable P] {a c : String} {b : Option String}
    (h : (if P then some a else b) = some c) : P ∨ b = some c := by
  by_cases hp : P
  · exact .inl hp
  · simp only [hp, ↓reduceIte] at h; exact .inr h

theorem ite_none {P : Prop} [Decidable P] {x : Option String} {c : String}
    (h : (if P then x else none) = some c) : P ∧ x = some c := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
  · simp only [hp, ↓reduceIte] at h; cases h

/-- `classify` is sound: a classified word is in the proved subset. Each branch is one
`stepOK_<class>` theorem, applied to the branch's conditions. -/
theorem classify_sound {w : Nat} {c : String} (h : classify w = some c) : StepOK w := by
  rw [classify] at h
  obtain ⟨hw, h⟩ := ite_none h
  rcases ite_some h with hc | h
  · exact stepOK_addSubImm hw hc
  rcases ite_some h with hc | h
  · exact stepOK_addSubShifted hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_addSubExt hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_addSubCarry hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_logicalShifted hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_logicalImm hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_moveWide hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_bitfield hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_extr hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_pcrel hw hc
  rcases ite_some h with hc | h
  · exact stepOK_condSel hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_condCmpReg hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_condCmpImm hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_madd hw hc
  rcases ite_some h with hc | h
  · exact stepOK_maddl hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_mulh hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_div hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_shiftV hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_rbit hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_clz hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_cls hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_rev16 hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_rev32 hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact stepOK_rev64 hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact stepOK_b hw hc
  rcases ite_some h with hc | h
  · exact stepOK_bcond hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_cb hw hc
  rcases ite_some h with hc | h
  · exact stepOK_tb hw hc
  rcases ite_some h with hc | h
  · exact stepOK_br hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_blr hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact stepOK_ret hw hc.1 hc.2
  cases h


/-- `fpClassify` is sound: a classified floating-point word is `FPStepOK`. -/
theorem fpClassify_sound {w : Nat} {c : String} (h : fpClassify w = some c) : FPStepOK w := by
  rw [fpClassify] at h
  obtain ⟨hw, h⟩ := ite_none h
  rcases ite_some h with hc | h
  · exact fpStepOK_fcmp hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.2.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fmul hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fdiv hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fadd hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fsub hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fmadd hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fmsub hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fnmadd hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fnmsub hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fsqrt hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fccmp hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fcvt hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_scvtf hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_ucvtf hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fcvtzs hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_fcvtzu hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
  cases h

theorem covered_words (p : Program) (h : covered p = true) :
    ∀ w ∈ p.segments.flatMap (·.words), StepOK w := by
  intro w hw
  obtain ⟨seg, hs, hws⟩ := List.mem_flatMap.mp hw
  simp only [covered, Bool.and_eq_true, List.all_eq_true] at h
  have := ((h.1 seg hs).2 w hws)
  cases hc : classify w with
  | none => rw [hc] at this; cases this
  | some c => exact classify_sound hc

theorem covered_code (p : Program) (h : covered p = true) :
    ∀ seg ∈ p.segments, seg.base + 4 * seg.words.length < 2 ^ 56 := by
  intro seg hs
  simp only [covered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact (h.1 seg hs).1

theorem covered_stubs (p : Program) (h : covered p = true) : ∀ st ∈ p.stubs, st.addr < 2 ^ 56 := by
  intro st hs
  simp only [covered, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 st hs

theorem classify_sound_fp {w : Nat} {c : String} (h : classify w = some c) : FPStepOK w := by
  rw [classify] at h
  obtain ⟨hw, h⟩ := ite_none h
  rcases ite_some h with hc | h
  · exact fpStepOK_addSubImm hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_addSubShifted hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_addSubExt hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_addSubCarry hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_logicalShifted hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_logicalImm hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_moveWide hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_bitfield hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_extr hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_pcrel hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_condSel hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_condCmpReg hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_condCmpImm hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_madd hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_maddl hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_mulh hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_div hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_shiftV hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_rbit hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_clz hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_cls hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_rev16 hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_rev32 hw hc.1 hc.2.1 hc.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_rev64 hw hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  rcases ite_some h with hc | h
  · exact fpStepOK_b hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_bcond hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_cb hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_tb hw hc
  rcases ite_some h with hc | h
  · exact fpStepOK_br hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_blr hw hc.1 hc.2
  rcases ite_some h with hc | h
  · exact fpStepOK_ret hw hc.1 hc.2
  cases h


/-- `fpClassify` is sound: a classified floating-point word is `FPStepOK`. -/
theorem classifyAll_sound {w : Nat} {c : String} (h : classifyAll w = some c) : FPStepOK w := by
  unfold classifyAll at h
  cases hc : classify w with
  | some c' => exact classify_sound_fp hc
  | none => rw [hc] at h; exact fpClassify_sound h

theorem coveredAll_words (p : Program) (h : coveredAll p = true) :
    ∀ w ∈ p.segments.flatMap (·.words), FPStepOK w := by
  intro w hw
  obtain ⟨seg, hs, hws⟩ := List.mem_flatMap.mp hw
  simp only [coveredAll, Bool.and_eq_true, List.all_eq_true] at h
  have := ((h.1 seg hs).2 w hws)
  cases hc : classifyAll w with
  | none => rw [hc] at this; cases this
  | some c => exact classifyAll_sound hc

theorem coveredAll_code (p : Program) (h : coveredAll p = true) :
    ∀ seg ∈ p.segments, seg.base + 4 * seg.words.length < 2 ^ 56 := by
  intro seg hs
  simp only [coveredAll, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact (h.1 seg hs).1

theorem coveredAll_stubs (p : Program) (h : coveredAll p = true) : ∀ st ∈ p.stubs, st.addr < 2 ^ 56 := by
  intro st hs
  simp only [coveredAll, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 st hs


open Lean Elab Command in
/-- `janus_asl_corollary C of T using W`: add the theorem `C` whose type and proof are
`JanusAudit.aslCorollary T W` (the kernel checks it on `addDecl`). -/
elab "janus_asl_corollary " c:ident " of " t:ident " using " w:ident : command => do
  liftTermElabM do
    let (ty, val) ← JanusAudit.aslCorollary t.getId w.getId
    addDecl (.thmDecl { name := c.getId, levelParams := [], type := ty, value := val })

end JanusASL.Verify
