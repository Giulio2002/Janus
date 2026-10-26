import Janus
import Extracted

/-!
# `Has32(m map[uint32]bool, k uint32) bool` on amd64

As on arm64, under `MapVarAmd64.Access1F32` with `vs = 1`; the key is the low 32 bits of the
argument register (`MOVL BX, CX`, then `MapVarAmd64.key32`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64
  Janus.Contracts.MapVarAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x13)

/-- The return address the call at `Extracted.entry + 0x1a` pushes. -/
def ret1f : Nat := Extracted.entry + 0x1f

/-- The precondition. -/
def pre (M : MapModel (BitVec 32) (BitVec (8 * 1))) (m : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1)))
    (s : State) : Prop :=
  CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1)))
    (hl : M.Laws)
    (hacc : Access1F32 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast32") 1 M)
    (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k] (pre M m f)
      (fun _ s' => (s'.regs 0).toNat = ((f (k.setWidth 32)).getD 0).toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast32"]
  have hfw : MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret1f)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)] := by janus_frame
  janus_eval_nat hR : ret1f
  simp only [hR] at hfw
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc hfw (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window hfw (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 1 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus64_run
    have hkk : ((k.setWidth 32).setWidth 64).setWidth 32 = k.setWidth 32 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
    simp only [key32, setRegF, reduceIte, Nat.reduceEqDiff, hkk]
    have := ((f (k.setWidth 32)).getD 0#8).isLt
    omega

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: `ME1` (`MapModel0.ME` with 1-byte values), the code `MapSatAmd64.zsCode` behind a
`JMP` at the contract's address, and a lookup of the key `7` in the non-nil map `MP`: the
result is `false`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64
open Janus.Contracts.MapVar (SlotHoldsN)

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

theorem ME1_empty {K : Type} {m : Janus.Arm64.Memory} {mp : Nat} {f : AMap K (BitVec 8)}
    (h : IsMap (ME1 K) m mp f) : f = AMap.empty := by
  unfold IsMap at h
  split at h
  · exact h
  · exact h.2.1

theorem mmem64_rep1 : (ME1 (BitVec 32)).Rep mmem64 MP AMap.empty := ⟨rfl, rfl, by decide, by decide⟩

/-- The first byte of the zero value is `0`. -/
theorem zs1 {m : Janus.Arm64.Memory} (hze : ZEnv m) : SlotHoldsN (ME1 (BitVec 32)) m ZS 1 0 := by
  refine ⟨Janus.Arm64.Memory.accessible_mono _ hze.1 (Nat.le_refl _) (by decide),
    inPriv0 (by decide) (by decide), ?_⟩
  rw [← Janus.Arm64.Memory.readLE_mod _ ZS 8 1 (by decide), hze.2]

theorem access1F32_impl1 : Access1F32 (toy.link (at0 zsCode)) A0 1 (ME1 (BitVec 32)) := by
  rw [link_at0]
  intro f s hpc hpre
  obtain ⟨⟨hze, hg, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩, -, hmap⟩ := hpre
  have hf := ME1_empty hmap
  subst hf
  janus64_run
  exact Janus.Contracts.MapStr.mapReturn64_of (ME1 _) 3 [] _ s _ _ (by simp [retAddrOf])
    (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl
    (MemFrame.refl _ _) hze (fun _ _ _ h => h) ⟨hmap, zs1 hze⟩

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1_fast32"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := zsCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Access1F32 (Extracted.program.link implAt) cAddr 1 (ME1 (BitVec 32)) := by
  have hA : Access1F32 (Extracted.program.link implAt) A0 1 (ME1 (BitVec 32)) := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (access1F32_impl1 f)
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

def mv : BitVec 64 := BitVec.ofNat 64 MP
def kv : BitVec 64 := 7#64

/-- The witness call state: `Has32(MP, 7)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kv
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (ME1 (BitVec 32)) mv AMap.empty s0 := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 mmem64_rep1⟩
  · simp only [ME1, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [ME1, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 32) (BitVec (8 * 1)))
    (ret : Nat) (s : State) (m k : BitVec 64) (f : AMap (BitVec 32) (BitVec (8 * 1))),
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
