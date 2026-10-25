import Extracted

/-!
# `type:.hash.FKey`: the compiler-generated hash of `struct { F float64; S string }` (arm64)

**Guarantee.** For every hash model `H` (`HashModel`: the process's hash as an uninterpreted
function), every `f64hash` and `strhash` satisfying `Hash.Fhash`/`Hash.Strhash`, and every call
state with the key and its string readable and outside the stack window and the runtime's
memory: the hash returned is `strhash` of the string seeded with `f64hash` of the float
(`KeyHash`). **The law maps need** (`keyHash_congr`, `hash_of_keyEq`): keys that are equal under
Go's `==` (as decided by the generated `type:.eq.FKey`, proved in `EqFKey`) have the same possible
hashes, including `+0` and `-0` (`HashLaws.fhashIs_of_feq`); a NaN key is equal to nothing and may
hash to anything (`HashLaws.fhashIs_nan`).
-/

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

/-- With the key equality the compiler generates for `FKey` (`type:.eq.FKey`, proved in the
`EqFKey` example: the floats `feq`, then the strings `strEq`): keys it calls equal hash alike. -/
theorem hash_of_keyEq (H : HashModel) {m : Memory} {p q h r : Nat}
    (he : (feq binary64 (m.readLE p 8) (m.readLE q 8) && strEq m (p + 8) (q + 8)) = true) :
    KeyHash H m p h r ↔ KeyHash H m q h r := by
  simp only [Bool.and_eq_true, strEq, beq_iff_eq] at he
  obtain ⟨hf, hl, hb⟩ := he
  exact keyHash_congr H hf hl hb

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `H0` (every hash is its seed), code for `f64hash` (`HashSat.f64hashCode` at `A0`, behind
a branch) and for `strhash` (`HashSat.seedCode`, at its address), and a call hashing the key at
`STR - 8` (`+0`, then the 8-byte string at `VAL`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.HashSat

def fAddr : Nat := Extracted.program.contractAddr "runtime.f64hash"
def sAddr : Nat := Extracted.program.contractAddr "runtime.strhash"
def tramp : Segment := { name := "tramp", base := fAddr, words := [branchWord fAddr A0] }
def strSeg : Segment := { name := "strhash", base := sAddr, words := seedCode }
def model0 : Segment := { name := "model", base := A0, words := f64hashCode }
def implAt : List Segment := [tramp, strSeg, model0]

theorem link_eq : Extracted.program.link implAt =
    (Extracted.program.link [tramp, strSeg]).link [model0] := by
  simp [Program.link, implAt]

theorem modelF (d : Nat) : Fhash (Extracted.program.link implAt) fAddr H0 d binary64 8 := by
  have hA : Fhash (Extracted.program.link implAt) A0 H0 d binary64 8 := by
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (f64hash_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : fAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem modelS (d : Nat) : Strhash (Extracted.program.link implAt) sAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨he, _, ⟨hl1, hl2, _⟩, _⟩, _⟩
  janus_eval_nat hC : sAddr
  rw [hC] at hpc
  janus_run
  exact seed_hRet he (by simp [setReg, seed_mod])

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The key at `STR - 8`, the seed 0. -/
def k : BitVec 64 := BitVec.ofNat 64 (STR - 8)
def h0 : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then k
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [k, h0] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : pre H0 64 k s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, wmem_henv _, ?_, ?_, rfl,
    by decide, by decide, ?_, ?_, by decide, by decide, ?_, ?_⟩ <;>
    simp only [window, callerWindow, H0_priv, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (H : HashModel) (d ret : Nat) (s : State) (p h : BitVec 64),
    H.Laws ∧ Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d
      binary64 8 ∧
    Strhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.strhash") H d ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [p, h] s ∧ pre H d p s :=
  ⟨implAt, H0, 64, ret, s0, k, h0, H0_laws, modelF 64, modelS 64, hret, setup, hpre⟩

/-- So the guarantee is reached: the result is a possible hash of the key. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ KeyHash H0 s0.mem (STR - 8) 0 (s'.regs 0).toNat :=
  (correctness implAt H0 H0_laws 64 (modelF 64) (modelS 64) k h0 ret hret s0 setup hpre).mono
    fun _ h => ⟨h.1, h.2⟩

end Witness

end Proof
