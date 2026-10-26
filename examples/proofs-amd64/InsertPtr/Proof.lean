import Janus
import Extracted

/-!
# `InsertPtr(m map[*PNode]uint64, p *PNode, v uint64)` sets `m[p] = v` (amd64)

As on arm64, under `MapVarAmd64.Assign64Ptr` (8-byte values) and a readiness predicate `H` at
entry (`RSP` of the call `40` bytes below the entry's).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x19)

/-- The precondition. -/
def pre (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (m k : BitVec 64)
    (f : AMap (BitVec 64) (BitVec 64)) (s : State) : Prop :=
  CallerOK M s 40 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
    H [mapType, m.toNat, k.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (Contracts.rtView M.priv s.mem)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (H : Contracts.RtReady) (hasn : Contracts.MapVarAmd64.Assign64Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64ptr") 8 M H)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (pre M H m k f)
      (fun s s' => M.Rep s'.mem m.toNat (f.set k v) ∧ M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign_fast64ptr"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by simp [setRegF, keepABI, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide),
     by simpa [setRegF] using hty, by simpa [setRegF] using hm0, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp40]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    simpa using hH
  · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 40))
      (n := M.depth + 40 + 32) (by omega) (by omega))
    janus64_run
    exact ⟨(hset v).1, (hset v).2.1⟩

/-! ## Non-vacuity: every hypothesis of `correctness` holds together

As on arm64: the model `MapModel0.MC ck64`, the readiness `MapModel0.HAssign`, its code
`MapSatAmd64.assignCode` behind a `JMP` at the contract's address, and a call inserting the
pointer `VAL` with value `42` into the empty map `MP`. -/

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceModel
  Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.MapVarSatAmd64

def cAddr : Nat := Extracted.program.contractAddr "runtime.mapassign_fast64ptr"

def tramp : Janus.Amd64.Segment := { name := "tramp", base := cAddr, bytes := jmpBytes cAddr A0 }
def model0 : Janus.Amd64.Segment := { name := "model", base := A0, bytes := assignCode }
def implAt : List Janus.Amd64.Segment := [tramp, model0]

theorem link_eq : Extracted.program.link implAt = (Extracted.program.link [tramp]).link [model0] := by
  simp [Janus.Amd64.Program.link, implAt]

theorem model : Contracts.MapVarAmd64.Assign64Ptr (Extracted.program.link implAt) cAddr 8 (MC ck64) HAssign := by
  have hA : Contracts.MapVarAmd64.Assign64Ptr (Extracted.program.link implAt) A0 8 (MC ck64) HAssign := by
    intro f
    rw [link_eq]
    exact Summary.of_codeIn64 (codeIn_link64 _ model0 (by decide)) (assign64Ptr_impl f)
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
def kv : BitVec 64 := BitVec.ofNat 64 VAL
def v : BitVec 64 := 42#64

/-- The witness call state: `InsertPtr(MP, VAL, 42)`. -/
def s0 : State :=
  { regs := fun i => if i = 0 then mv else if i = 3 then kv else if i = 1 then v
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mmem64 }

theorem setup : CallSetup ((Extracted.program.link implAt).withExit ret) Extracted.entry [mv, kv, v] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem pre0 : pre (MC ck64) HAssign mv kv AMap.empty s0 := by
  refine ⟨⟨mmem64_zenv, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, ?_, ?_, ?_⟩, trivial, by decide, mmem64_repC _, hAssign_mmem64 _ _ _⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

/-- All hypotheses of `correctness` are satisfiable together. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (H : Contracts.RtReady) (ret : Nat) (s : State) (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)),
    M.Laws ∧ Contracts.MapVarAmd64.Assign64Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64ptr") 8 M H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [m, k, v] s ∧
    pre M H m k f s :=
  ⟨implAt, MC _, HAssign, ret, s0, mv, kv, v, AMap.empty, MC_laws _, model, hret, setup, pre0⟩

/-- So the guarantee is reached: the map now holds `VAL ↦ 42`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (MC ck64).Rep s'.mem MP (AMap.empty.set kv 42#64) :=
  correctness implAt (MC _) (MC_laws _) HAssign model mv kv v AMap.empty ret hret s0 setup pre0
    |>.mono fun _ h => ⟨h.1, h.2.1⟩

end Witness

end Proof
