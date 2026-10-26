import Extracted

/-!
# `Has32(m map[uint32]bool, k uint32) bool` (arm64)

**Guarantee.** For every model `M` of the map runtime with 1-byte values (a `bool` is the byte
`0` or `1`) and every `mapaccess1_fast32` satisfying `MapVar.Access1F32` with `vs = 1`, every
map value `m` holding `f`, and every call state satisfying `CallerOK`: the call returns the
value byte of `f` under the 32-bit key `k` (`0`, i.e. `false`, if absent or `m` is nil).
The key is the low 32 bits of the argument register (`MapVar.key32`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map Janus.Contracts.MapVar

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Has32" 8)
    (segWord Extracted.program "example.com/basic.Has32" 9) 0

/-- The precondition. -/
def pre (M : MapModel (BitVec 32) (BitVec (8 * 1))) (m : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1)))
    (s : State) : Prop :=
  CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f

theorem correctness (impl : List Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1))) (hl : M.Laws)
    (hacc : Access1F32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast32") 1 M)
    (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k] (pre M m f)
      (fun _ s' => (s'.regs 0).toNat = ((f (k.setWidth 32)).getD 0).toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast32"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
     by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48)) (hi := s.sp.toNat + 0)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 1 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, key32] at hs3
    exact hs3

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

A model with 1-byte values (`ME1`: `MapModel0.ME` with `BitVec 8` values: one empty, non-nil
map at `MP`, the zero value at `ZS`), code meeting `Access1F32` for it (`MapSat.zsCode` at
`IfaceSat.A0`, reached from the contract's address by a branch), an admissible return address,
and a call state looking up the key `7` in the non-nil map `MP`: `correctness` applies
(`returns`: the result is `false`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat

/-- `MapModel0.ME` with 1-byte values. -/
def ME1 (K : Type) : MapModel K (BitVec 8) where
  Rep m mp f := mp = MP ∧ f = AMap.empty ∧ m.accessible MP 8 false = true ∧ m.readLE MP 8 = 0
  Iter _ _ _ _ ks := ks.length ≤ 1
  Typ _ := True
  Env m _ := ZEnv m
  priv := priv0
  depth := 64

theorem ME1_laws (K : Type) : (ME1 K).Laws where
  rep_frame m m' mp f h ha := by
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact ⟨h1, h2, by rw [ha.accessible]; exact h3,
      (readLE_of_agrees ha (by decide) (by decide)).trans h4⟩
  iter_frame _ _ _ _ _ _ h _ := h
  env_frame m m' _ h ha := ZEnv.frame h ha
  len m mp f h := by
    obtain ⟨rfl, rfl, h3, h4⟩ := h
    exact ⟨h3, by decide, fun ks hk => by rw [h4, hk.eq_nil_of_empty]; rfl⟩
  finite m mp f h := by
    obtain ⟨-, rfl, -, -⟩ := h
    exact ⟨[], keys_empty⟩

theorem ME1_empty {K : Type} {m : Memory} {mp : Nat} {f : AMap K (BitVec 8)}
    (h : IsMap (ME1 K) m mp f) : f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact h
  · exact h.2.1

theorem mmem_rep1 : (ME1 (BitVec 32)).Rep mmem MP AMap.empty := ⟨rfl, rfl, by decide, by decide⟩

/-- The first byte of the zero value is `0`. -/
theorem zs1 {m : Memory} (hze : ZEnv m) : SlotHoldsN (ME1 (BitVec 32)) m ZS 1 0 := by
  refine ⟨Memory.accessible_mono _ hze.1 (Nat.le_refl _) (by decide), inPriv0 (by decide) (by decide), ?_⟩
  rw [← Memory.readLE_mod _ ZS 8 1 (by decide), hze.2]

theorem access1F32_impl1 : Access1F32 (toy.link (at0 zsCode)) A0 1 (ME1 (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hc, hout⟩, -, hmap⟩ := hpre
  obtain ⟨hl1, hl2, -⟩ := hc
  have hf := ME1_empty hmap
  subst hf
  janus_run
  exact mapReturn_of (ME1 _) 3 [] _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg])
    (by simp [setReg]) rfl rfl rfl rfl (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, zs1 hze⟩

/-- `runtime.mapaccess1_fast32`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1_fast32"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := zsCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : Access1F32 (Extracted.program.link implAt) cAddr 1 (ME1 (BitVec 32)) := by
  have hA : Access1F32 (Extracted.program.link implAt) A0 1 (ME1 (BitVec 32)) := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (access1F32_impl1 f)
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

/-- The map `MP` and the key `7`. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def kv : BitVec 64 := 7#64

/-- The witness call state: `Has32(MP, 7)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then kv
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre0 : pre (ME1 (BitVec 32)) mv AMap.empty s0 := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 mmem_rep1⟩
  · simp only [ME1, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [ME1, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1))) (ret : Nat)
    (s : State) (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))),
    M.Laws ∧ Access1F32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast32") 1 M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, k] s ∧
    m.toNat ≠ 0 ∧ pre M m f s :=
  ⟨implAt, ME1 _, ret, s0, mv, kv, AMap.empty, ME1_laws _, model, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the lookup in the empty map gives `false`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 := by
  refine (correctness implAt (ME1 _) (ME1_laws _) model mv kv AMap.empty ret hret s0 setup pre0).mono ?_
  intro s' h
  exact ⟨h.1, by simpa [AMap.empty] using h.2⟩

end Witness

end Proof
