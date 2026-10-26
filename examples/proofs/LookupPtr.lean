import Extracted

/-!
# `LookupPtr(m map[*PNode]uint64, p *PNode) uint64` (arm64)

**Guarantee.** For every model `M` of the map runtime and every `mapaccess1_fast64` satisfying
`Map.Access1` (pointer keys are 8-byte words, so a `map[*T]V` uses the `_fast64` lookups on the
same model as `mapassign_fast64ptr`), every map value `m` holding `f` and every call state
satisfying `CallerOK`: the call returns `f p`, `0` if `p` is absent (or `m` is nil).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.LookupPtr" 8)
    (segWord Extracted.program "example.com/basic.LookupPtr" 9) 0

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64))
    (s : State) : Prop :=
  CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hacc : Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M)
    (m p : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, p] (pre M m f)
      (fun _ s' => s'.regs 0 = (f p).getD 0) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast64"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
     by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48)) (hi := s.sp.toNat + 0)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hs3
    rw [hs3]; simp

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

The model `MapModel0.ME` (one empty, non-nil map at `MP`), code meeting `Access1` for it
(`MapSat.zsCode` at `IfaceSat.A0`, reached from the contract's address by a branch), an
admissible return address, and a call state looking up the pointer `VAL` in the non-nil map
`MP`: `correctness` applies (`returns`: the result is `0`). -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSat Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSat

/-- `runtime.mapaccess1_fast64`'s address. -/
def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1_fast64"

/-- The branch at the contract's address and the model code. -/
def tramp : Segment := { name := "tramp", base := cAddr, words := [branchWord cAddr A0] }
def model0 : Segment := { name := "model", base := A0, words := zsCode }
def implAt : List Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Program.link, implAt]

theorem model : Access1 (Extracted.program.link implAt) cAddr (ME (BitVec 64)) := by
  have hA : Access1 (Extracted.program.link implAt) A0 (ME (BitVec 64)) := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn (codeIn_link _ model0 (by decide)) (access1_impl f)
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

/-- The map `MP` and the key pointer `VAL`. -/
def mv : BitVec 64 := BitVec.ofNat 64 MP
def pv : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `LookupPtr(MP, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 1 then pv
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mmem }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, pv] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem pre0 : pre (ME (BitVec 64)) mv AMap.empty s0 := by
  refine ⟨⟨mmem_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 (mmem_rep _)⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Disjoint; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (ret : Nat)
    (s : State) (m p : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
    M.Laws ∧ Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, p] s ∧
    m.toNat ≠ 0 ∧ pre M m f s :=
  ⟨implAt, ME _, ret, s0, mv, pv, AMap.empty, ME_laws _, model, hret, setup, by decide, pre0⟩

/-- So the guarantee is reached: the lookup in the empty map gives `0`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 := by
  refine (correctness implAt (ME _) (ME_laws _) model mv pv AMap.empty ret hret s0 setup pre0).mono ?_
  intro s' h
  exact ⟨h.1, by simpa [AMap.empty] using h.2⟩

end Witness

end Proof
