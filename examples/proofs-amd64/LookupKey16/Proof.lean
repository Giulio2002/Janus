import Janus
import Extracted

/-!
# `LookupKey16(m, kp)` returns `m[*kp]` for `[16]byte` keys (the generic `mapaccess2`) (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, with the 16 key bytes at `kp` readable and outside the stack window, the result is the value stored under the key read little-endian from `kp` (`0` if absent) and the presence flag.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.MapAmd64` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted RIP-relative `LEA`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x16)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 128) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2") M)
    (m kp : BitVec 64) (f : AMap (BitVec 128) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp]
      (fun s => CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        Buffer s kp 16 false ∧
        Janus.Spec.Disjoint kp.toNat 16 ((s.regs 4).toNat - (M.depth + 40)) (M.depth + 40 + 8))
      (fun s s' =>
        let key := BitVec.ofNat 128 (s.mem.readLE kp.toNat 16)
        s'.regs 0 = (f key).getD 0 ∧ (s'.regs 3).toNat % 256 = (f key).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, ⟨hk1, hk2⟩, hkd⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout hkd
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapaccess2"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF]) (by simpa using hs.zero)
      (by simpa using hs.df) (by simp [setRegF, keepABI, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), by simpa [setRegF] using hty, ?_, ?_⟩ ?_
  · simp only [setRegF]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := (s.regs 4).toNat - (M.depth + 40))
      (hi := (s.regs 4).toNat + 8) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · simp only [setRegF, reduceIte, Nat.reduceEqDiff, Arm64.Memory.accessible_writeLE, calleeStack, hsp40,
      outside_cons, outside_nil, and_true]
    exact ⟨hk2, by omega, by omega⟩
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus64_run
    all_goals simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hs3 hok
    all_goals (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at hs3)
    all_goals (repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)] at hok)
    all_goals first | exact hok | exact ⟨by rw [hs3]; simp, hok⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMapAmd64.lean` sits at `runtime.mapaccess2`'s address in this program;
`janus64_map_access2ptr` proves `Access2Ptr` for it (the model `ME`: one empty non-nil map) by running the stub code. Below, a
concrete call state of `LookupKey16(map, key)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.LiveStubMapAmd64
open Janus.Contracts.IfaceModel (wsp wg wret)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapaccess2"))
theorem addr : Extracted.program.contractAddr "runtime.mapaccess2" = cA := by decide
def implAt : List Janus.Amd64.Segment := [accessSeg cA]
def linked : Janus.Amd64.Program := Extracted.program.link implAt

theorem h0 : Access2Ptr linked cA (ME (BitVec 128)) := by janus64_map_access2ptr

theorem hcon : Access2Ptr (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapaccess2") (ME (BitVec 128)) := by
  rw [addr]; exact h0

def emp128 : AMap (BitVec 128) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Janus.Arm64.Memory := Janus.Contracts.LiveStubMap.withData mmem64 dat

def ret : Nat := wret

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 3 then BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (ME (BitVec 128)) s0 40 8 := by
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Janus.Spec.Disjoint, ME_depth]; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (ME (BitVec 128)) s0 40 8 ∧ (ME (BitVec 128)).Typ mapType ∧ IsMap (ME (BitVec 128)) s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    Buffer s0 (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL) 16 false ∧ Janus.Spec.Disjoint (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL).toNat 16 ((s0.regs 4).toNat - ((ME (BitVec 128)).depth + 40)) ((ME (BitVec 128)).depth + 40 + 8) :=
  ⟨callerOK, trivial, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, by decide, by decide⟩, by unfold Buffer; decide,
    by simp only [Janus.Spec.Disjoint, ME_depth]; decide⟩

theorem rtpre_pc {K V : Type} {M : MapModel K V} {n : Nat} {s : Janus.Amd64.State} (a : BitVec 64) (h : RTPre M n s) :
    RTPre M n { s with rip := a } := by
  obtain ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩ := h
  exact ⟨e, ⟨g1, g2, g3⟩, c1, c2, c3, c4, c5, c6, c7, o⟩

/-- The precondition of `Access2Ptr`'s summary at the call state `s_c` (one conjunct: the audit matches the whole pre). -/
@[reducible] def Access2PtrSite (M : MapModel (BitVec 128) (BitVec 64)) (f : AMap (BitVec 128) (BitVec 64)) (s_c : Janus.Amd64.State) : Prop :=
  RTPre M 3 s_c ∧ M.Typ (s_c.regs 0).toNat ∧ IsMap M s_c.mem (s_c.regs 3).toNat f ∧
    s_c.mem.accessible (s_c.regs 1).toNat 16 false = true ∧ Outside (s_c.regs 1).toNat 16 (calleeStack s_c M.depth 3)

/-- The call state of the `mapaccess2` contract (U-WITNESS-CALLSITE): the stock witness state of `MapSatAmd64`, at the contract address. -/
def wsCall : Janus.Amd64.State := { mstate64 mmem64 (args (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL) 0) with rip := BitVec.ofNat 64 cA }

theorem wsCall_pre : Access2PtrSite (ME (BitVec 128)) AMap.empty wsCall :=
  ⟨rtpre_pc _ (mstate64_rtpre _ rfl rfl mmem64 rfl _ 3 (by decide) mmem64_zenv mmem64_guard mmem64_ret), trivial,
    (isMap_of_ne (by decide)).2 (mmem64_rep _), by decide,
    by simp only [Janus.Contracts.MapAmd64.calleeStack, ME_depth, outside_cons, outside_nil, and_true]; decide⟩

/-- The theorem fires: `LookupKey16(map, key)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (let key := BitVec.ofNat 128 (s0.mem.readLE (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL).toNat 16)
    s'.regs 0 = (emp128 key).getD 0 ∧ (s'.regs 3).toNat % 256 = (emp128 key).isSome.toNat) :=
  correctness implAt (ME (BitVec 128)) (ME_laws _) hcon (BitVec.ofNat 64 MP) (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL) AMap.empty ret hret s0 setup pre

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapaccess2`
meeting `Access2Ptr` for it, and a call state of `LookupKey16(map, key)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 128) (BitVec 64)) (ret : Nat)
    (s : Janus.Amd64.State), M.Laws ∧
    Access2Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL] s ∧
    (CallerOK M s 40 8 ∧ M.Typ mapType ∧ IsMap M s.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    Buffer s (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL) 16 false ∧ Janus.Spec.Disjoint (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL).toNat 16 ((s.regs 4).toNat - (M.depth + 40)) (M.depth + 40 + 8)) ∧
    (∃ (f : AMap (BitVec 128) (BitVec 64)) (s_c : Janus.Amd64.State),
      s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mapaccess2") ∧ Access2PtrSite M f s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧
    (let key := BitVec.ofNat 128 (s.mem.readLE (BitVec.ofNat 64 Janus.Contracts.IfaceModel.VAL).toNat 16)
    s'.regs 0 = (emp128 key).getD 0 ∧ (s'.regs 3).toNat % 256 = (emp128 key).isSome.toNat) :=
  ⟨implAt, (ME (BitVec 128)), ret, s0, (ME_laws _), hcon, hret, setup, pre, ⟨AMap.empty, wsCall, by show BitVec.ofNat 64 cA = _; rw [addr], wsCall_pre⟩, returns⟩

end Witness

end Proof
