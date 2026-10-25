import Janus
import Extracted

/-!
# `type:.hash.FKey` on amd64: the compiler-generated hash of `struct { F float64; S string }`

As on arm64, under `HashAmd64.Fhash`/`HashAmd64.Strhash`, with the same laws.
-/

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

/-- The return address the call at `Extracted.entry + 0x18` pushes. -/
def ret18 : Nat := Extracted.entry + 0x18

/-- The return address the call at `Extracted.entry + 0x2c` pushes. -/
def ret2c : Nat := Extracted.entry + 0x2c

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
      (BitVec.toNat (s.regs 4) - 32) 8 ret18) (MemAmd64.callerWindow s d 32 16) := by
    simp only [MemAmd64.callerWindow]; janus_frame
  janus_eval_nat hR18 : ret18
  simp only [hR18] at hfw
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
        (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 ret2c).readLE a n = s.mem.readLE a n := by
      intro a n h1 h2
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        hfr.readLE a n (by simp only [outside_append, outside_cons, outside_nil, and_true]; exact ⟨h1, by omega, by omega⟩),
        hfw.readLE a n (by simp only [outside_cons, outside_nil, and_true]; exact h2)]
    janus_eval_nat hR2c : ret2c
    simp only [hR2c] at hm'
    have hacc : ∀ a n w, (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 ret2c).accessible a n w =
        s.mem.accessible a n w := fun a n w => by
      rw [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hfw.accessible]
    janus_eval_nat hR2c : ret2c
    simp only [hR2c] at hacc
    have hp' : p.toNat + 8 = (p + 8#64).toNat := by rw [BitVec.toNat_add]; simp; omega
    have hptr : strPtr (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 ret2c) (p.toNat + 8) =
        strPtr s.mem (p.toNat + 8) := by
      unfold strPtr; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    janus_eval_nat hR2c : ret2c
    simp only [hR2c] at hptr
    have hlen : strLen (m'.writeLE (BitVec.toNat (s.regs 4) - 32) 8 ret2c) (p.toNat + 8) =
        strLen s.mem (p.toNat + 8) := by
      unfold strLen; exact hm' _ _ (Outside.of_sub hpp (by omega) (by omega)) (by omega)
    janus_eval_nat hR2c : ret2c
    simp only [hR2c] at hlen
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
          (BitVec.toNat (s.regs 4) - 32) 8 ret18).readLE p.toNat 8 = s.mem.readLE p.toNat 8 :=
        hfw.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      janus_eval_nat hR18 : ret18
      simp only [hR18] at hx
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

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `H0`, `HashSatAmd64.f64hashCode` behind a `JMP` at `runtime.f64hash`'s
address, `HashSatAmd64.seedCode` at `runtime.strhash`'s, and the key at `STR - 8`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.HashSatAmd64

def fAddr : Nat := Extracted.program.contractAddr "runtime.f64hash"
def sAddr : Nat := Extracted.program.contractAddr "runtime.strhash"
def tramp : Janus.Amd64.Segment := { name := "tramp", base := fAddr, bytes := jmpBytes fAddr A0 }
def strSeg : Janus.Amd64.Segment := { name := "strhash", base := sAddr, bytes := seedCode }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := f64hashCode }
def implAt : List Janus.Amd64.Segment := [tramp, strSeg, model0]

theorem link_eq : Extracted.program.link implAt =
    (Extracted.program.link [tramp, strSeg]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem modelF (d : Nat) : HashAmd64.Fhash (Extracted.program.link implAt) fAddr H0 d binary64 8 := by
  have hA : HashAmd64.Fhash (Extracted.program.link implAt) A0 H0 d binary64 8 := by
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (f64hash_impl d)
  intro s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : fAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA _ rfl ⟨⟨e, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

theorem modelS (d : Nat) : HashAmd64.Strhash (Extracted.program.link implAt) sAddr H0 d := by
  rw [show Extracted.program.link implAt =
    { Extracted.program with segments := Extracted.program.segments ++ implAt } from rfl]
  intro s hpc ⟨⟨henv, hg, ⟨hal, hd1, hd2, hst, hx15, hdf, hra⟩, hout, hgo, hgp⟩, _⟩
  janus_eval_nat hC : sAddr
  rw [hC] at hpc
  janus64_run
  seed_close hdf

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

def k : BitVec 64 := BitVec.ofNat 64 (STR - 8)
def h0 : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then k
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [k, h0] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : pre H0 64 k s0 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide,
    by simp only [outside_cons, outside_nil, and_true]; decide⟩, wmem64_henv _, ?_, ?_,
    by unfold GoMXCSR; decide, by decide, by decide, ?_, ?_, by decide, by decide, ?_, ?_⟩ <;>
    simp only [window, MemAmd64.callerWindow, H0_priv, outside_cons, outside_nil, and_true] <;> decide

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (H : HashModel) (d ret : Nat) (s : State)
    (p h : BitVec 64), H.Laws ∧
    HashAmd64.Fhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.f64hash") H d
      binary64 8 ∧
    HashAmd64.Strhash (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.strhash") H d ∧
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
