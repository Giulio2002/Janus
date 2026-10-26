import Janus
import Extracted

/-!
# `LookupPtr(m map[*PNode]uint64, p *PNode) uint64` on amd64

As on arm64, under `MapAmd64.Access1` (the `_fast64` lookup of 8-byte pointer keys).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x14)

/-- The return address the call at `Extracted.entry + 0x20` pushes. -/
def ret25 : Nat := Extracted.entry + 0x25

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (m : BitVec 64) (f : AMap (BitVec 64) (BitVec 64))
    (s : State) : Prop :=
  CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (hacc : Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M)
    (m p : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, p] (pre M m f)
      (fun _ s' => s'.regs 0 = (f p).getD 0) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast64"]
  have hfw : MemFrame s.mem ((Arm64.Memory.writeLE s.mem (BitVec.toNat (s.regs 4) - 8) 8
      (BitVec.toNat (s.regs 5))).writeLE (BitVec.toNat (s.regs 4) - 40) 8 ret25)
      [((s.regs 4).toNat - (M.depth + 40), (s.regs 4).toNat + 8)] := by janus_frame
  janus_eval_nat hR : ret25
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
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus64_run
    all_goals try simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hs3
    all_goals first | (rw [hs3]; simp) | simp [hs3]

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapModel0.ME`, its code `MapSatAmd64.zsCode` behind a `JMP` at the
contract's address, and a lookup of the pointer `VAL` in the non-nil map `MP`: the result is
`0`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapaccess1_fast64"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := zsCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Access1 (Extracted.program.link implAt) cAddr (ME (BitVec 64)) := by
  have hA : Access1 (Extracted.program.link implAt) A0 (ME (BitVec 64)) := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (access1_impl f)
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
def pv : BitVec 64 := BitVec.ofNat 64 VAL

/-- The witness call state: `LookupPtr(MP, VAL)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then pv
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, pv] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (ME (BitVec 64)) mv AMap.empty s0 := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, (isMap_of_ne (by decide)).2 (mmem64_rep _)⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together, with a non-nil map. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (ret : Nat) (s : State) (m p : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
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
