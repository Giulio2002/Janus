import Extracted

/-!
# `LookupK24(m map[[24]byte]uint64, k *[24]byte) uint64` (arm64)

**Guarantee.** For every model `M` of the map runtime and every generic `mapaccess1` satisfying
`MapVar.Access1G` for 24-byte keys and 8-byte values, every map value `m` holding `f`, and every
call state in which the map type's key type is 24 bytes of regular memory (`KeyRegular`: so the
type's hash is the seeded byte hash and its equality compares the bytes) and the key `*k` is
readable and outside the stack window: the call returns `f`'s value under the key's 24 bytes
(`MapVar.keyAt`), `0` if absent (or `m` is nil).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar Janus.Contracts.MapStr Janus.Contracts.MapVar Janus.Spec.Type

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.LookupK24" 9)
    (segWord Extracted.program "example.com/basic.LookupK24" 10) 0

/-- The stack window of `LookupK24` and the runtime call. -/
def window {K V : Type} (M : MapModel K V) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (M.depth + 48), s.sp.toNat)]

/-- The precondition. -/
def pre (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8))) (m kp : BitVec 64)
    (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) (s : State) : Prop :=
  CallerOK M s 48 0 ∧ M.Typ mapType ∧ KeyRegular (rtView M.priv s.mem) mapType 24 ∧
    IsMap M s.mem m.toNat f ∧
    kp.toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible kp.toNat 24 false = true ∧
    Outside kp.toNat 24 (window M s)

theorem correctness (impl : List Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
    (hl : M.Laws) (hacc : Access1G (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1") 24 8 M)
    (m kp : BitVec 64) (f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp] (pre M m kp f)
      (fun s s' => s'.regs 0 = (f (keyAt s.mem kp.toNat 24)).getD 0) := by
  intro ret hret s hs ⟨hc, hty, hreg, hmap, hkb, hka, hko⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hreg
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  simp only [window, outside_cons, outside_nil, and_true] at hko
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess1"]
  have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; try simp
  have hfw : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE
      (BitVec.toNat s.sp - 56) 8 (BitVec.toNat (s.regs 29)))
      [(s.sp.toNat - (M.depth + 48), s.sp.toNat + 0)] := by janus_frame
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide)
      (by decide), by simpa [setReg] using hty, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
    repeat rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hreg
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · simpa [setReg] using hkb
  · simpa [setReg, hfw.accessible] using hka
  · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, calleeStack, hsp, outside_cons,
      outside_nil, and_true]
    omega
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    have hk := hfw.readLE kp.toNat 24 (by simp only [outside_cons, outside_nil, and_true]; omega)
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, keyAt, hk] at hs3
    rw [hs3]; simp [keyAt]

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model (`MK`: `MapModel0.ME`'s one empty, non-nil map at `MP` and zero value at `ZS`, with
24-byte keys and a private memory that also holds the key-type word of the real `mapType`
descriptor), a witness memory in which that word points to a key type `KT24` of 24 bytes of
regular memory, code meeting `Access1G` for the model (`MapSat.zsCode` at `IfaceSat.A0`, reached
from the contract's address by a branch), an admissible return address, and a call state
looking up the 24 bytes at `VAL` in the non-nil map `MP`: `correctness` applies (`returns`: the
result is `0`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat

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

theorem agrees0 {m m' : Memory} (ha : Agrees m m' privK) : Agrees m m' priv0 :=
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

theorem MK_empty {m : Memory} {mp : Nat} {f : AMap (BitVec (8 * 24)) (BitVec (8 * 8))}
    (h : IsMap MK m mp f) : f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact h
  · exact h.2.1

theorem access1G_implK : Access1G (toy.link (at0 zsCode)) A0 24 8 MK := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, -, hmap, -⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := MK_empty hmap
  subst hf
  have hz : SlotHoldsN MK s.mem MapModel0.ZS 8 0 :=
    ⟨hze.1, (inPriv0 (by decide) (by decide)).append_left _, hze.2⟩
  janus_run
  exact MapSat.mapReturn_of MK 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, hz⟩

/-- `runtime.mapaccess1`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := zsCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : Access1G (Extracted.program.link implAt) cAddr 24 8 MK := by
  have hA : Access1G (Extracted.program.link implAt) A0 24 8 MK := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (access1G_implK f)
  intro f s hpc hpre
  rw [link_eq] at hA ⊢
  obtain ⟨r, sp, pc, fl, mem, dz, vr, tp, fc, fs⟩ := s
  janus_eval_nat hC : cAddr
  simp only [hC] at hpc
  subst hpc
  janus_run until [A0]
  obtain ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩ := hpre
  exact hA f _ rfl ⟨⟨he, ⟨g1, g2, g3⟩, hrest⟩, hrest'⟩

/-- The witness return address. -/
def ret : Nat := wret

theorem hret : RetAddr (Extracted.program.link implAt) ret := RetAddr.of_check (by decide)

/-- The witness memory: `mmem`, the key type `KT24`, and the key-type word of `mapType`
(read-only, holding `KT24`). -/
def mmemK : Memory :=
  ⟨fun a => if a = mapType + 49 then 0x0d else if a = mapType + 50 then 0x01
      else if a = KT24 then 24 else if a = KT24 + 20 then 8 else mmem.bytes a,
    mmem.regions ++ [⟨mapType + 48, 8, false⟩]⟩

/-- The map `MP` and the key pointer `VAL`. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def kp : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `LookupK24(MP, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kp
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmemK }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kp] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre0 : pre MK mv kp AMap.empty s0 := by
  janus_eval_nat hT : mapType
  have hR : ∀ a n, 0x10000 ≤ a → a + n ≤ 0x11000 → (rtView MK.priv mmemK).readLE a n = mmemK.readLE a n :=
    fun a n h1 h2 => readLE_rtView ((inPriv0 h1 h2).append_left _)
  have hW : (rtView MK.priv mmemK).readLE (mapType + 48) 8 = KT24 := by
    rw [readLE_rtView ⟨(mapType + 48, mapType + 56), by simp [MK, privK], Nat.le_refl _, Nat.le_refl _⟩]
    simp only [mmemK, KT24, hT]; decide
  refine ⟨⟨?_, ⟨by decide, ?_, ?_⟩, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩, trivial,
    ⟨?_, ?_⟩, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, ?_, ?_⟩, by decide, ?_, ?_⟩
  all_goals first
    | (unfold KeyRegular keyType tySize isRegularMemory tyTFlag; rw [hW, hR _ _ (by decide) (by decide)]
       try rw [hR _ _ (by decide) (by decide)]
       simp only [mmemK, KT24, hT]; decide)
    | (simp only [s0, MK, privK, priv0, window, Disjoint, ZEnv, mmemK, hT, outside_cons, outside_nil,
        outside_append, and_true, regG, stackguard0Offset, Memory.accessible, Memory.readLE]; decide)

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec (8 * 24)) (BitVec (8 * 8)))
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
