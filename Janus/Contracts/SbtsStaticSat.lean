import Janus.Contracts.SbtsLiveSatAmd64

/-!
# `slicebytetostringSpecT` is satisfiable (U-SBTS-STATIC)

`slicebytetostringSpecT st` is `slicebytetostringSpec st` with `StaticTable st mem` in its precondition. A spec whose
precondition no state meets would give vacuous theorems, so this file proves (both ISAs) that it is met: a witness
memory `tmem` holding the `staticuint64s` identity table (a closed-form byte function: the 256 words `8 * b` apart hold
`b`, in a read-only region at `ST`), an implementation (`RET`, the empty-string shape), and a call state over `tmem`
meeting `RtLivePre`, the table included.
-/

namespace Janus.Contracts.SbtsStaticSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.SbtsLiveSat
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

/-- Where the witness keeps the identity table. -/
def ST : Nat := 0x40000000

def tbytes (a : Nat) : Byte :=
  if ST ≤ a ∧ a < ST + 2048 then (if (a - ST) % 8 = 0 then BitVec.ofNat 8 ((a - ST) / 8) else 0) else wbytes a

/-- The witness memory plus the table: a read-only region of 256 words at `ST`. -/
def tmem : Memory := ⟨tbytes, wmem.regions ++ [⟨ST, 2048, false⟩]⟩

set_option maxRecDepth 100000 in
theorem tmem_static : StaticTable ST tmem := by
  intro b hb
  have : ∀ b, b < 256 → tmem.readLE (ST + 8 * b) 8 = b := by decide +kernel
  exact this b hb


/-- The witness call state over `tmem`: argument words `l` in `X0..`. -/
def tst (l : List Nat) : State := { wst l with mem := tmem }

theorem tmem_inv (g : Nat) : toyInv tys0 0x400 [] g (view (toyRt tys0) [] tmem) := by
  refine ⟨HEAP, by decide, Nat.le_refl _, by decide, by decide, fun r hr => absurd hr (by simp),
    fun i hi hi' => ?_, by decide, by decide, by decide, fun t ht => ?_⟩
  · rw [Memory.readLE_one]
    have : (view (toyRt tys0) [] tmem).bytes i = 0 := by
      simp only [view, tmem, tbytes, wbytes]
      split
      · have e0 : ¬ (ST ≤ i ∧ i < ST + 2048) := by simp only [ST, HEAP, HEND, HSIZE] at *; omega
        have e1 : i ≠ BUMP + 3 := by simp only [BUMP, HEAP, HEND, HSIZE] at *; omega
        have e2 : i ≠ tyA := by simp only [tyA, HEAP, HEND] at *; omega
        have e3 : i ≠ tyB := by simp only [tyB, HEAP, HEND] at *; omega
        have e4 : i ≠ tyC := by simp only [tyC, HEAP, HEND] at *; omega
        have e5 : i ≠ tyC + 8 := by simp only [tyC, HEAP, HEND] at *; omega
        simp [e0, e1, e2, e3, e4, e5]
      · rfl
    rw [this]; rfl
  · simp only [tys0, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem tst_mem (l : List Nat) : (tst l).mem = tmem := rfl
theorem t28 (l : List Nat) : (tst l).regs 28 = BitVec.ofNat 64 wg := by simp [tst, wst, wstate]
theorem t30 (l : List Nat) : (tst l).regs 30 = BitVec.ofNat 64 wret := by simp [tst, wst, wstate]
theorem tsp (l : List Nat) : (tst l).sp = BitVec.ofNat 64 wsp := rfl

theorem tcallOK (l : List Nat) (n : Nat) (hn : n ≤ 5) : CallOK (tst l) 4096 n := by
  have hw : tmem.accessible (wsp - 4096) (4096 + 8 + 8 * 5) true = true := by decide
  simp only [CallOK, t30, tsp, tst_mem, wspn]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by simp [wsp]; omega, ?_⟩
  exact Memory.accessible_mono _ hw (Nat.le_refl _) (by omega)

theorem tguard (l : List Nat) (n : Nat) (hn : n ≤ 5) : StackRoom (tst l) 4096 n := by
  simp only [StackRoom, Janus.Spec.GuardOK, t28, tsp, tst_mem, wspn, wgn, calleeStack]
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true, wsp, wg]
  omega

theorem twin (l : List Nat) (n : Nat) (hn : n ≤ 5) :
    LiveSep (calleeStack (tst l) 4096 n) (toyRt tys0) := by
  intro x hx
  simp only [calleeStack, tsp, wspn, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;>
    simp only [toyRt, tys0, outside_cons, outside_nil, outside_append, List.map, and_true, wsp, HEAP, HEND, BUMP, WBUF,
      tyA, tyB, tyC] <;> omega

set_option maxRecDepth 20000 in
theorem sbtsT_impl (st : Nat) :
    RtLiveContract (toy.link (at0 [0xd65f03c0])) A0 4096 (toyR tys0 okSb) (slicebytetostringSpecT st)
      slicebytetostringLive := by
  rw [link_at0]
  intro L b s hpc pre
  have ⟨⟨h30a, h30b, _, _, _, _, _⟩, _⟩ := pre
  obtain ⟨-, -, -, -, -, hok, hinv, -⟩ := pre
  janus_run
  have ha : argWords s 3 = [0, 0, 0] := (hok.2 : argWords s 3 = [0, 0, 0])
  have ha' := ha
  simp [argWords, wordsFrom] at ha'
  have e0 : (s.regs 0).toNat = 0 := ha'.1
  have e1 : (s.regs 1).toNat = 0 := ha'.2.1
  refine rt_post_nochange ?_ ?_ ?_ ?_ hinv
  · simp [slicebytetostringSpecT, slicebytetostringSpec, slicebytetostringLive, ha, arg, roundupsize_zero']
  · simp [slicebytetostringSpecT, slicebytetostringSpec, slicebytetostringLive, ha, arg, e0, e1]
  · simp [slicebytetostringSpecT, slicebytetostringSpec, slicebytetostringLive, ha, arg, e0, e1, range0]
  · simp only [slicebytetostringSpecT, slicebytetostringSpec, ha, e0, e1, arg, List.getD_cons_succ, List.getD_cons_zero]
    simp [Janus.Spec.strBytes, StrOut, StrAt]

theorem slicebytetostringSpecT_satisfiable : ∃ (st : Nat) (impl : List Segment) (R : RtInv),
    RtLiveContract (toy.link impl) A0 4096 R (slicebytetostringSpecT st) slicebytetostringLive ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      RtLivePre 4096 R (slicebytetostringSpecT st) slicebytetostringLive A0 L b s := by
  have ha : argWords (tst [0, 0, 0]) 3 = [0, 0, 0] := by decide
  refine ⟨ST, at0 [0xd65f03c0], toyR tys0 okSb, sbtsT_impl ST, [], 0x400, tst [0, 0, 0], rfl,
    tcallOK _ 3 (by omega), ?_, ?_, by trivial, tguard _ 3 (by omega),
    ⟨⟨rfl, ha⟩, tmem_inv 0, ?_, by simp, twin _ 3 (by omega)⟩⟩
  · simp only [slicebytetostringSpecT, slicebytetostringSpec, ha, arg, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨⟨Or.inl rfl, by simp [StrIn], fun h => absurd rfl h⟩, tst_mem _ ▸ tmem_static⟩
  · intro x hx
    simp [slicebytetostringSpecT, slicebytetostringSpec, ha, arg] at hx
    subst hx
    simp [calleeStack, tsp, wspn, wsp]
  · have hn : (slicebytetostringSpecT ST).nargs = 3 := rfl
    simp [slicebytetostringLive, hn, ha, arg, roundupsize_zero']

end Janus.Contracts.SbtsStaticSat
