import Janus
import Extracted

/-!
# `LookupK24(m map[[24]byte]uint64, k *[24]byte) uint64` on amd64

As on arm64, under the generic `MapVarAmd64.Access1G` for 24-byte keys of regular memory
(`KeyRegular`) and 8-byte values.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapVarAmd64 Janus.Spec.Type
open Janus.Contracts.MapVar (KeyRegular keyAt keyType SlotHoldsN)
open Janus.Contracts (rtView rtView_writeLE readLE_rtView)

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x16)

/-- The return address the call at `Extracted.entry + 0x20` pushes. -/
def ret25 : Nat := Extracted.entry + 0x25

/-- The stack window of `LookupK24` and the runtime call (amd64). -/
def window {K V : Type} (M : MapModel K V) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)]

/-- The precondition. -/
def pre (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (m kp : BitVec 64)
    (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s : State) : Prop :=
  CallerOK M s 40 8 ∧ M.Typ mapType ∧ KeyRegular (rtView M.priv s.mem) mapType 24 ∧
    IsMap M s.mem m.toNat f ∧
    kp.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat 24 false = true ∧
    Outside kp.toNat 24 (window M s)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (hl : M.Laws) (hacc : Access1G (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1") 24 8 M)
    (m kp : BitVec 64) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp] (pre M m kp f)
      (fun s s' => s'.regs 0 = (f (keyAt s.mem kp.toNat 24)).getD 0) := by
  intro ret hret s hs ⟨hc, hty, hreg, hmap, hkb, hka, hko⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hreg
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  simp only [window, outside_cons, outside_nil, and_true] at hko
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess1"]
  have hfw : MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret25)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)] := by janus_frame
  janus_eval_nat hR : ret25
  simp only [hR] at hfw
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hreg
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setRegF] using hkb
  · simpa [setRegF, hfw.accessible] using hka
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, calleeStack, hsp40, outside_cons,
      outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    have hk := hfw.readLE kp.toNat 24 (by simp only [outside_cons, outside_nil, and_true]; omega)
    janus64_run
    all_goals try simp only [setRegF, reduceIte, Nat.reduceEqDiff, keyAt, hk] at hs3
    all_goals first | (rw [hs3]; simp [keyAt]) | (simp [keyAt, hk, hs3])

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MK` (`MapModel0.ME` with 24-byte keys, whose private memory also holds
the key-type word of the real `mapType`), a witness memory `mmemK` (`mmem64` with that word
pointing to a 24-byte regular-memory key type `KT24`), the code `MapSatAmd64.zsCode` behind a
`JMP` at the contract's address, and a lookup of the 24 bytes at `VAL` in `MP`: the result is
`0`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64

/-- The key type of the witness: `Size_ = 24`, `TFlag = TFlagRegularMemory`. -/
def KT24 : Nat := 0x10d00

/-- The model's private memory: `priv0` and the key-type word of `mapType`. -/
def privK : List (Nat × Nat) := priv0 ++ [(mapType + 48, mapType + 56)]

/-- `MapModel0.ME` with 24-byte keys and the private memory `privK`. -/
def MK : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)) where
  Rep m mp f := mp = MP ∧ f = AMap.empty ∧ m.accessible MP 8 false = true ∧ m.readLE MP 8 = 0
  Iter _ _ _ _ ks := ks.length ≤ 1
  Typ _ := True
  Env m _ := ZEnv m
  priv := privK
  depth := 64

theorem agrees0 {m m' : Janus.Arm64.Memory} (ha : Agrees m m' privK) : Agrees m m' priv0 :=
  ⟨ha.1, fun a h => ha.2 a (h.append_left _)⟩

theorem MK_laws : MK.Laws where
  rep_frame m m' mp f h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by rw [ha.accessible]; exact h3,
      (readLE_of_agrees (agrees0 ha) (by decide) (by decide)).trans h4⟩
  iter_frame _ _ _ _ _ _ h _ := h
  env_frame m m' _ h ha := ZEnv.frame h (agrees0 ha)
  len m mp f h := by
    obtain ⟨rfl, rfl, h3, h4⟩ := h
    exact ⟨h3, by decide, fun ks hk => by rw [h4, hk.eq_nil_of_empty]; rfl⟩
  finite m mp f h := by
    obtain ⟨-, rfl, -, -⟩ := h
    exact ⟨[], keys_empty⟩

theorem MK_empty {m : Janus.Arm64.Memory} {mp : Nat} {f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))}
    (h : IsMap MK m mp f) : f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact h
  · exact h.2.1

theorem access1G_implK : Access1G (toy.link (at0 zsCode)) A0 24 8 MK := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, -, hmap, -⟩ := hpre
  have hf := MK_empty hmap
  subst hf
  have hz : SlotHoldsN MK s.mem Janus.Contracts.MapModel0.ZS 8 0 :=
    ⟨hze.1, (inPriv0 (by decide) (by decide)).append_left _, hze.2⟩
  janus64_run
  exact Janus.Contracts.MapStr.mapReturn64_of MK 3 [] _ s _ _ (by simp [retAddrOf]) (by simp [setRegF])
    (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl (MemFrame.refl _ _) hze
    (fun _ _ _ h => h) ⟨hmap, hz⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := zsCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Access1G (Extracted.program.link implAt) cAddr 24 8 MK := by
  have hA : Access1G (Extracted.program.link implAt) A0 24 8 MK := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (access1G_implK f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, rip, fl, xm, mem, yh, fsb, df, mx⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus64_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `mmem64`, the key type `KT24`, and the key-type word of `mapType`
(read-only, holding `KT24`). -/
def mmemK : Janus.Arm64.Memory :=
  ⟨fun a => if a = mapType + 49 then 0x0d else if a = mapType + 50 then 0x01
      else if a = KT24 then 24 else if a = KT24 + 20 then 8 else mmem64.bytes a,
    mmem64.regions ++ [⟨mapType + 48, 8, false⟩]⟩

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `LookupK24(MP, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kp
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmemK }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp] s0 :=
  ⟨rfl, by janus_eval_nat hT : mapType; simp only [s0, mmemK, hT]; decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre MK mv kp AMap.empty s0 := by
  janus_eval_nat hT : mapType
  have hR : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → (rtView MK.priv mmemK).readLE a n = mmemK.readLE a n :=
    fun a n h1 h2 => readLE_rtView ((inPriv0 h1 h2).append_left _)
  have hW : (rtView MK.priv mmemK).readLE (mapType + 48) 8 = KT24 := by
    rw [readLE_rtView ⟨(mapType + 48, mapType + 56), by simp [MK, privK], Nat.le_refl _, Nat.le_refl _⟩]
    simp only [mmemK, KT24, hT]; decide
  refine ⟨⟨?_, ⟨by decide, ?_, ?_⟩, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩, trivial,
    ⟨?_, ?_⟩, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, ?_, ?_⟩, by decide, ?_, ?_⟩
  all_goals first
    | (unfold KeyRegular keyType tySize isRegularMemory tyTFlag; rw [hW, hR _ _ (by decide) (by decide)]
       try rw [hR _ _ (by decide) (by decide)]
       simp only [mmemK, KT24, hT]; decide)
    | (simp only [s0, MK, privK, priv0, window, Janus.Spec.Disjoint, ZEnv, mmemK, hT, outside_cons,
        outside_nil, outside_append, and_true, regG, regSP, stackguard0Offset, Janus.Arm64.Memory.accessible,
        Janus.Arm64.Memory.readLE]; decide)

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (ret : Nat) (s : State) (m kp : BitVec 64) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))),
    M.Laws ∧ Access1G (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1") 24 8 M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, kp] s ∧
    m.toNat ≠ 0 ∧ pre M m kp f s :=
  ⟨implAt, MK, ret, s0, mv, kp, AMap.empty, MK_laws, model, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the lookup in the empty map gives `0`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 := by
  refine (correctness implAt MK MK_laws model mv kp AMap.empty ret hret s0 setup pre0).mono ?_
  intro s' h
  exact ⟨h.1, by simpa [AMap.empty] using h.2⟩

end Witness

end Proof
