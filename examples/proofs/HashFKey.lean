import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.Hash Janus.Float

namespace Proof

/-- The possible hashes of the `FKey` at `p` in `m` with seed `h`: `f64hash` of the `float64` at
`p`, then `strhash` of the string header at `p + 8` with that hash as the seed. -/
def KeyHash (H : HashModel) (m : Memory) (p h r : Nat) : Prop :=
  ∃ h1, FHashIs H binary64 8 (m.readLE p 8) h h1 ∧
    r = H.mem h1 (strLen m (p + 8)) (m.readLE (strPtr m (p + 8)) (strLen m (p + 8)))

/-- The stack window of the hash function and its runtime calls. -/
def window (d : Nat) (s : State) : List (Nat × Nat) := callerWindow s d 32 16

/-- The precondition: see the module documentation. -/
def pre (H : HashModel) (d : Nat) (p : BitVec 64) (s : State) : Prop :=
  CallerOK s d 32 16 ∧ H.Env s.mem (s.regs 28) ∧ Outside (s.sp.toNat - (d + 32)) (d + 48) H.priv ∧
    Outside ((s.regs 28).toNat + 16) 8 H.priv ∧ s.fpcr = 0 ∧
    p.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 24 false = true ∧
    Outside p.toNat 24 (window d s) ∧ Outside p.toNat 24 H.priv ∧
    strPtr s.mem (p.toNat + 8) + strLen s.mem (p.toNat + 8) ≤ 2 ^ 48 ∧
    s.mem.accessible (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) false = true ∧
    Outside (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) (window d s) ∧
    Outside (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) H.priv

theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d : Nat)
    (hf : Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d
      binary64 8)
    (hs : Strhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.strhash") H d)
    (p h : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, h] (pre H d p)
      (fun s s' => KeyHash H s.mem p.toNat h.toNat (s'.regs 0).toNat) := by
  intro ret hret s hs0 ⟨hc, henv, hpriv, hgp, hfp, hpb, hpa, hpo, hpp, hsb, hsa, hso, hsp'⟩
  have hc' := hc
  obtain ⟨⟨hg1, hg2, hg3⟩, hal, hd8, hdd, hb, hst, hog⟩ := hc'
  janus_intro hs0
  simp only [regG, stackguard0Offset, stackguard0] at hg1 hg2 hg3
  have hp8 : Outside p.toNat 8 (callerWindow s d 32 16) := Outside.of_sub hpo (Nat.le_refl _) (by omega)
  have hso0 := hso
  simp only [window, callerWindow, outside_cons, outside_nil, and_true] at hog hpo hso
  have hsp : (s.sp - 32#64).toNat = s.sp.toNat - 32 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  janus_run until [Extracted.program.contractAddr "runtime.f64hash"]
  have hfw : MemFrame s.mem (((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE
      (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat)
      (callerWindow s d 32 16) := by
    simp only [callerWindow]; janus_frame
  have hfw0 := hfw
  simp only [callerWindow, outside_cons, outside_nil, and_true] at hfw
  have E := fun {S : State} (hf : MemFrame s.mem S.mem (callerWindow s d 32 16))
      (hsp : S.sp.toNat = s.sp.toNat - 32) (hg : S.regs 28 = s.regs 28)
      (hlr : (S.regs 30).toNat % 4 = 0) (hlr' : (S.regs 30).toNat < 2 ^ 48) =>
    EqPre.of_caller (nargs := 2) hc hf hsp hg hlr hlr' (by decide) (by decide)
  refine Reaches.call (Summary.withExit hf hret) rfl
    ⟨⟨?_, (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).1,
      (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).2.1, ?_,
      (E hfw0 (by simp [hsp]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg])).2.2,
      by simpa [setReg] using hgp⟩, rfl, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := s.sp.toNat - (d + 32)) (hi := s.sp.toNat + 16)
      (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
  · simp only [hsp]; exact Outside.of_sub hpriv (by omega) (by omega)
  · exact Input.of_caller (s := s) (d := d) (frame := 32) (above := 16) hfw0 (by simp [hsp]) (by decide)
      (by omega) (by simpa [setReg, h_x0] using (show p.toNat + 8 ≤ 2 ^ 48 by omega))
      (by simpa [setReg, h_x0] using Memory.accessible_mono _ hpa (Nat.le_refl _) (by omega))
      (by simpa [setReg, h_x0] using hp8)
  · intro s' hpc' ⟨r, v, fl, fs, m', hs', hfr, henv', hres⟩
    subst hs'
    simp only [calleeStack, hsp] at hfr
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x1] at hres
    janus_run until [Extracted.program.contractAddr "runtime.strhash"]
    have hm' : ∀ a n, Outside a n H.priv → a + n ≤ s.sp.toNat - (d + 32) ∨ s.sp.toNat + 16 ≤ a →
        m'.readLE a n = s.mem.readLE a n := by
      intro a n h1 h2
      rw [hfr.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, by omega, by omega⟩),
        hfw.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact h2)]
    have hacc : ∀ a n w, m'.accessible a n w = s.mem.accessible a n w := fun a n w => by
      rw [hfr.accessible, hfw.accessible]
    have hp' : p.toNat + 8 = (p + 8#64).toNat := by rw [BitVec.toNat_add]; simp; omega
    have hptr : strPtr m' (p.toNat + 8) = strPtr s.mem (p.toNat + 8) := by
      unfold strPtr; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    have hlen : strLen m' (p.toNat + 8) = strLen s.mem (p.toNat + 8) := by
      unfold strLen; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    refine Reaches.call (Summary.withExit hs hret) rfl
      ⟨⟨?_, (EqPre.of_parts (nargs := 2) hc hacc ?_ (by simp [hsp]) (by simp [setReg, Map.keepABI])
          (by simp [setReg]) (by simp [setReg]) (by decide) (by decide)).1,
        (EqPre.of_parts (nargs := 2) hc hacc ?_ (by simp [hsp]) (by simp [setReg, Map.keepABI])
          (by simp [setReg]) (by simp [setReg]) (by decide) (by decide)).2.1, ?_,
        (EqPre.of_parts (nargs := 2) hc hacc ?_ (by simp [hsp]) (by simp [setReg, Map.keepABI])
          (by simp [setReg]) (by simp [setReg]) (by decide) (by decide)).2.2,
        by simpa [setReg, Map.keepABI] using hgp⟩, ?_, ?_⟩ ?_
    all_goals try exact hm' _ _ hgp (by omega)
    · simpa [setReg, Map.keepABI] using henv'
    · simp only [hsp]; exact Outside.of_sub hpriv (by omega) (by omega)
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, ← hp']
      refine ⟨by omega, by rw [hacc]; exact Memory.accessible_mono _ hpa (by omega) (by omega), ?_⟩
      simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, ← hp', hptr, hlen]
      refine ⟨hsb, by rw [hacc]; exact hsa, ?_⟩
      simp only [calleeStack, hsp, outside_cons, outside_nil, and_true]; omega
    · intro s2 hpc2 ⟨r2, v2, fl2, fs2, m2, hs2, hfr2, henv2, hres2⟩
      subst hs2
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, ← hp', hptr, hlen] at hres2
      rw [hm' _ _ hsp' (by omega)] at hres2
      simp only [calleeStack, hsp, setReg_apply, reduceIte, Nat.reduceEqDiff] at hfr2
      janus_run
      have hx : (((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE (BitVec.toNat s.sp - 40) 8
          (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 p.toNat).readLE p.toNat 8 =
          s.mem.readLE p.toNat 8 :=
        hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      rw [hx] at hres
      exact ⟨_, hres, hres2⟩

/-- **The hash law a map relies on.** Two `FKey`s that are equal under Go's `==` (the floats
`==`, i.e. equal values with `+0 = -0`, never a NaN; the strings of equal length and bytes) have
the same possible hashes, whatever memory they live in and whatever their string data pointers:
so a map finds a key equal to the one it stored. A NaN key is not `==` to anything, and indeed its
hash may be anything (`HashLaws.fhashIs_nan`). -/
theorem keyHash_congr (H : HashModel) {m₁ m₂ : Memory} {p₁ p₂ h r : Nat}
    (hf : feq binary64 (m₁.readLE p₁ 8) (m₂.readLE p₂ 8) = true)
    (hl : strLen m₁ (p₁ + 8) = strLen m₂ (p₂ + 8))
    (hb : m₁.readLE (strPtr m₁ (p₁ + 8)) (strLen m₁ (p₁ + 8)) =
      m₂.readLE (strPtr m₂ (p₂ + 8)) (strLen m₂ (p₂ + 8))) :
    KeyHash H m₁ p₁ h r ↔ KeyHash H m₂ p₂ h r := by
  unfold KeyHash
  have hx : m₁.readLE p₁ 8 < 2 ^ binary64.width := Memory.readLE_lt m₁ p₁ 8
  have hy : m₂.readLE p₂ 8 < 2 ^ binary64.width := Memory.readLE_lt m₂ p₂ 8
  rw [hl, ← hl, hb]
  constructor
  · rintro ⟨h1, h1f, rfl⟩
    exact ⟨h1, (HashLaws.fhashIs_of_feq H binary64 8 h h1 hx hy hf).1 h1f, by rw [hl]⟩
  · rintro ⟨h1, h1f, rfl⟩
    exact ⟨h1, (HashLaws.fhashIs_of_feq H binary64 8 h h1 hx hy hf).2 h1f, by rw [hl]⟩

end Proof
