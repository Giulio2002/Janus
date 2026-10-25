import Janus
import Extracted

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts Janus.Contracts.Mem
  Janus.Contracts.Hash Janus.Float
open Janus (MemFrame Outside outside_cons outside_nil outside_append)

namespace Proof

/-- The possible hashes of the `FKey` at `p` in `m` with seed `h` (as on arm64). -/
def KeyHash (H : HashModel) (m : Janus.Arm64.Memory) (p h r : Nat) : Prop :=
  ∃ h1, FHashIs H binary64 8 (m.readLE p 8) h h1 ∧
    r = H.mem h1 (strLen m (p + 8)) (m.readLE (strPtr m (p + 8)) (strLen m (p + 8)))

/-- The stack window of the hash function and its runtime calls (amd64). -/
def window (d : Nat) (s : State) : List (Nat × Nat) := MemAmd64.callerWindow s d 32 16

/-- The precondition: see the module documentation. -/
def pre (H : HashModel) (d : Nat) (p : BitVec 64) (s : State) : Prop :=
  MemAmd64.CallerOK s d 32 16 ∧ H.Env s.mem (s.regs 14) ∧
    Outside ((s.regs 4).toNat - (d + 32)) (d + 48) H.priv ∧
    Outside ((s.regs 14).toNat + 16) 8 H.priv ∧ GoMXCSR s ∧
    p.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 24 false = true ∧
    Outside p.toNat 24 (window d s) ∧ Outside p.toNat 24 H.priv ∧
    strPtr s.mem (p.toNat + 8) + strLen s.mem (p.toNat + 8) ≤ 2 ^ 48 ∧
    s.mem.accessible (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) false = true ∧
    Outside (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) (window d s) ∧
    Outside (strPtr s.mem (p.toNat + 8)) (strLen s.mem (p.toNat + 8)) H.priv

set_option maxHeartbeats 2000000 in
theorem correctness (impl : List Segment) (H : HashModel) (hl : H.Laws) (d : Nat)
    (hf : HashAmd64.Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash")
      H d binary64 8)
    (hs : HashAmd64.Strhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.strhash")
      H d)
    (p h : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [p, h] (pre H d p)
      (fun s s' => KeyHash H s.mem p.toNat h.toNat (s'.regs 0).toNat) := by
  intro ret hret s hs0 ⟨hc, henv, hpriv, hgp, hfp, hpb, hpa, hpo, hpp, hsb, hsa, hso, hsp'⟩
  janus64_intro hs0
  have hc' := hc
  obtain ⟨hg, hal, hdd, hb, hst, hog⟩ := hc'
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr
  have hp8 : Outside p.toNat 8 (MemAmd64.callerWindow s d 32 16) := Outside.of_sub hpo (Nat.le_refl _) (by omega)
  simp only [window, MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hog hpo hso
  have hsp32 : (s.regs 4 - 32#64).toNat = (s.regs 4).toNat - 32 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.f64hash"]
  have hfw : MemFrame s.mem (((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE
      (BitVec.toNat (s.regs 4) - 32) 8 4745400) (MemAmd64.callerWindow s d 32 16) := by
    simp only [MemAmd64.callerWindow]; janus_frame
  have E := fun {S : State} (hf : MemFrame s.mem S.mem (MemAmd64.callerWindow s d 32 16))
      (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 32) (hg : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
      (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) =>
    MemAmd64.EqPre.of_caller (nargs := 2) hc hf hsp hg hx hdf hra (by decide) (by decide)
  have hfw0 := hfw
  simp only [MemAmd64.callerWindow, outside_cons, outside_nil, and_true] at hfw
  refine Reaches.call (Summary.withExit hf hret) rfl
    ⟨⟨?_, (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs0.zero) (by simpa using hs0.df)
        (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).1,
      (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs0.zero) (by simpa using hs0.df)
        (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).2.1, ?_,
      (E hfw0 (by simp [setRegF, hsp32]) (by simp [setRegF]) (by simpa using hs0.zero) (by simpa using hs0.df)
        (by simp [setRegF, hsp32, Janus.Arm64.Memory.readLE_writeLE_self])).2.2,
      by simpa [setRegF] using hgp⟩, hfp, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    exact hl.env_frame _ _ _ henv (Agrees.of_window (lo := (s.regs 4).toNat - (d + 32))
      (hi := (s.regs 4).toNat + 16) (by janus_frame) (Outside.of_sub hpriv (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]
    exact Outside.of_sub hpriv (by omega) (by omega)
  · exact MemAmd64.Input.of_caller hfw0 (by simp [setRegF, hsp32]) (by decide) (by omega)
      (by simpa [setRegF, h_a0] using (show p.toNat + 8 ≤ 2 ^ 48 by omega))
      (by simpa [setRegF, h_a0] using Janus.Arm64.Memory.accessible_mono _ hpa (Nat.le_refl _) (by omega))
      (by simpa [setRegF, h_a0] using hp8)
  · intro s' hpc' ⟨r, x, y, fl, mx, m', hs', hmx, hfr, henv', hres⟩
    subst hs'
    simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a1] at hres
    janus64_run until [Extracted.program.contractAddr "runtime.strhash"]
    have hm' : ∀ a n, Outside a n H.priv → a + n ≤ (s.regs 4).toNat - (d + 32) ∨ (s.regs 4).toNat + 16 ≤ a →
        (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 4745420).readLE a n = s.mem.readLE a n := by
      intro a n h1 h2
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hfr.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, by omega, by omega⟩),
        hfw.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact h2)]
    have hacc : ∀ a n w, (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 4745420).accessible a n w =
        s.mem.accessible a n w := fun a n w => by
      rw [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hfw.accessible]
    have hp' : p.toNat + 8 = (p + 8#64).toNat := by rw [BitVec.toNat_add]; simp; omega
    have hptr : strPtr (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 4745420) (p.toNat + 8) =
        strPtr s.mem (p.toNat + 8) := by
      unfold strPtr; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    have hlen : strLen (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 4745420) (p.toNat + 8) =
        strLen s.mem (p.toNat + 8) := by
      unfold strLen; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    have E2 := fun {S : State} (hacc : ∀ a n w, S.mem.accessible a n w = s.mem.accessible a n w)
        (hguard : S.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8)
        (hsp : (S.regs 4).toNat = (s.regs 4).toNat - 32) (hg : S.regs 14 = s.regs 14) (hx : S.xmm 15 = 0)
        (hdf : S.df = false) (hra : S.mem.readLE (S.regs 4).toNat 8 < 2 ^ 47) =>
      MemAmd64.EqPre.of_parts (nargs := 2) hc hacc hguard hsp hg hx hdf hra (by decide) (by decide)
    have hg' := hm' _ _ hgp (by omega)
    refine Reaches.call (Summary.withExit hs hret) rfl ⟨⟨?_, ?sg, ?co, ?_, ?gc, ?gp⟩, ?_, ?_⟩ ?_
    case sg =>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [regG, regSP, stackguard0Offset, stackguard0, setRegF, reduceIte, Nat.reduceEqDiff,
          MapAmd64.keepABI, false_or, or_true, ite_true, hacc, hg', hsp32] <;> omega
    case co =>
      refine ⟨?_, ?_, ?_, ?_, ?_, by simpa using hs0.df, ?_⟩ <;>
        simp only [setRegF, reduceIte, Nat.reduceEqDiff, MapAmd64.keepABI, MapAmd64.keepX15, hacc, hsp32,
          Janus.Arm64.Memory.readLE_writeLE_self] <;> try omega
      all_goals first
        | exact Janus.Arm64.Memory.accessible_mono _ hst (by omega) (by omega)
        | simpa using hs0.zero
        | decide
    case gc =>
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff,
        MapAmd64.keepABI, false_or, or_true, ite_true, hsp32, outside_cons, outside_nil, and_true]; omega
    case gp => simpa [setRegF, MapAmd64.keepABI] using hgp
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, MapAmd64.keepABI]
      exact hl.env_frame _ _ _ henv' (agrees_writeLE _ _ (Outside.of_sub hpriv (by omega) (by omega)))
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, hsp32]
      exact Outside.of_sub hpriv (by omega) (by omega)
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, ← hp']
      refine ⟨by omega, by rw [hacc]; exact Janus.Arm64.Memory.accessible_mono _ hpa (by omega) (by omega), ?_⟩
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
        outside_cons, outside_nil, and_true]; omega
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, ← hp', hptr, hlen]
      refine ⟨hsb, by rw [hacc]; exact hsa, ?_⟩
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32,
        outside_cons, outside_nil, and_true]; omega
    · intro s2 hpc2 ⟨r2, x2, y2, fl2, mx2, m2, hs2, hmx2, hfr2, henv2, hres2⟩
      subst hs2
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, ← hp', hptr, hlen] at hres2
      rw [hm' _ _ hsp' (by omega)] at hres2
      simp only [MemAmd64.calleeStack, MapAmd64.calleeStack, setRegF, reduceIte, Nat.reduceEqDiff, hsp32] at hfr2
      janus64_run
      have hx : (((Janus.Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
          (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) + 8) 8 p.toNat).writeLE
          (BitVec.toNat (s.regs 4) - 32) 8 4745400).readLE p.toNat 8 = s.mem.readLE p.toNat 8 :=
        hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      rw [hx] at hres
      exact ⟨_, hres, hres2⟩

/-- **The hash law a map relies on.** Two `FKey`s that are equal under Go's `==` (the floats
`==`, i.e. equal values with `+0 = -0`, never a NaN; the strings of equal length and bytes) have
the same possible hashes, whatever memory they live in and whatever their string data pointers:
so a map finds a key equal to the one it stored. A NaN key is not `==` to anything, and indeed its
hash may be anything (`HashLaws.fhashIs_nan`). -/
theorem keyHash_congr (H : HashModel) {m₁ m₂ : Janus.Arm64.Memory} {p₁ p₂ h r : Nat}
    (hf : feq binary64 (m₁.readLE p₁ 8) (m₂.readLE p₂ 8) = true)
    (hl : strLen m₁ (p₁ + 8) = strLen m₂ (p₂ + 8))
    (hb : m₁.readLE (strPtr m₁ (p₁ + 8)) (strLen m₁ (p₁ + 8)) =
      m₂.readLE (strPtr m₂ (p₂ + 8)) (strLen m₂ (p₂ + 8))) :
    KeyHash H m₁ p₁ h r ↔ KeyHash H m₂ p₂ h r := by
  unfold KeyHash
  have hx : m₁.readLE p₁ 8 < 2 ^ binary64.width := Janus.Arm64.Memory.readLE_lt m₁ p₁ 8
  have hy : m₂.readLE p₂ 8 < 2 ^ binary64.width := Janus.Arm64.Memory.readLE_lt m₂ p₂ 8
  rw [hl, ← hl, hb]
  constructor
  · rintro ⟨h1, h1f, rfl⟩
    exact ⟨h1, (HashLaws.fhashIs_of_feq H binary64 8 h h1 hx hy hf).1 h1f, by rw [hl]⟩
  · rintro ⟨h1, h1f, rfl⟩
    exact ⟨h1, (HashLaws.fhashIs_of_feq H binary64 8 h h1 hx hy hf).2 h1f, by rw [hl]⟩

/-- With the key equality the compiler generates for `FKey` (`type:.eq.FKey`, proved in the
`EqFKey` example: the floats `feq`, then the strings `strEq`): keys it calls equal hash alike. -/
theorem hash_of_keyEq (H : HashModel) {m : Janus.Arm64.Memory} {p q h r : Nat}
    (he : (feq binary64 (m.readLE p 8) (m.readLE q 8) && strEq m (p + 8) (q + 8)) = true) :
    KeyHash H m p h r ↔ KeyHash H m q h r := by
  simp only [Bool.and_eq_true, strEq, beq_iff_eq] at he
  obtain ⟨hf, hl, hb⟩ := he
  exact keyHash_congr H hf hl hb

end Proof
