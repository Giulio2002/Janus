import Extracted

/-!
# `LookupKey16(m, kp)` returns `m[*kp]` for `[16]byte` keys (the generic `mapaccess2`) (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, with the 16 key bytes at `kp` readable and outside the stack window, the result is the value stored under the key read little-endian from `kp` (`0` if absent) and the presence flag.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.Map` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted `ADRP`+`ADD` words.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map
  Janus.Contracts Janus.Contracts.Map

namespace Proof

def mapType : Nat :=
  adrpLdTarget (Extracted.entry + 0x24) (segWord Extracted.program "example.com/basic.LookupKey16" 9)
    (segWord Extracted.program "example.com/basic.LookupKey16" 10) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 128) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2") M)
    (m kp : BitVec 64) (f : AMap (BitVec 128) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, kp]
      (fun s => CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f ∧
        Ptr s.mem kp 16 false ∧ Disjoint kp.toNat 16 (s.sp.toNat - (M.depth + 48)) (M.depth + 48))
      (fun s s' =>
        let key := BitVec.ofNat 128 (s.mem.readLE kp.toNat 16)
        s'.regs 0 = (f key).getD 0 ∧ (s'.regs 1).toNat % 256 = (f key).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap, ⟨hk1, hk2⟩, hkd⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd hkd
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess2"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, ?_, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48)) (hi := s.sp.toNat + 0)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · have hsp : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
      rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, Memory.accessible_writeLE, calleeStack, hsp,
      outside_cons, outside_nil, and_true]
    exact ⟨hk1, by omega, by omega⟩
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    have hkey : ((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8
        (s.regs 29).toNat).readLE kp.toNat 16 = s.mem.readLE kp.toNat 16 := by
      rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, hkey] at hs3 hok
    exact ⟨by rw [hs3]; simp, hok⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMap.lean` sits at `runtime.mapaccess2`'s address in this program;
`janus_map_access2ptr` proves `Access2Ptr` for it (the model `ME`: one empty non-nil map) by running the stub code. Below, a
concrete call state of `LookupKey16(map, key)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.LiveStubMap
open Janus.Contracts.IfaceModel (wsp wg)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapaccess2"))
theorem addr : Extracted.program.contractAddr "runtime.mapaccess2" = cA := by decide
def implAt : List Segment := [accessSeg cA]
def linked : Program := Extracted.program.link implAt

theorem h0 : Access2Ptr linked cA (ME (BitVec 128)) := by janus_map_access2ptr

theorem hcon : Access2Ptr (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapaccess2") (ME (BitVec 128)) := by
  rw [addr]; exact h0

def dat : DataSegment := Extracted.data.head!
def mem0 : Memory := withData mmem dat

def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 1 then BitVec.ofNat 64 IfaceModel.VAL else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, BitVec.ofNat 64 IfaceModel.VAL] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (ME (BitVec 128)) s0 48 0 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Disjoint, ME_depth]; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (ME (BitVec 128)) s0 48 0 ∧ (ME (BitVec 128)).Typ mapType ∧ IsMap (ME (BitVec 128)) s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    Ptr s0.mem (BitVec.ofNat 64 IfaceModel.VAL) 16 false ∧ Disjoint (BitVec.ofNat 64 IfaceModel.VAL).toNat 16 (s0.sp.toNat - ((ME (BitVec 128)).depth + 48)) ((ME (BitVec 128)).depth + 48) :=
  ⟨callerOK, trivial, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, by decide, by decide⟩, by unfold Ptr; decide,
    by simp only [Disjoint, ME_depth]; decide⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapaccess2`
meeting `Access2Ptr` for it, and a call state of `LookupKey16(map, key)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 128) (BitVec 64)) (ret : Nat)
    (s : State), M.Laws ∧
    Access2Ptr (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, BitVec.ofNat 64 IfaceModel.VAL] s ∧
    (CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    Ptr s.mem (BitVec.ofNat 64 IfaceModel.VAL) 16 false ∧ Disjoint (BitVec.ofNat 64 IfaceModel.VAL).toNat 16 (s.sp.toNat - (M.depth + 48)) (M.depth + 48)) :=
  ⟨implAt, (ME (BitVec 128)), ret, s0, (ME_laws _), hcon, hret, setup, pre⟩

/-- The theorem fires: `LookupKey16(map, key)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (let key := BitVec.ofNat 128 (s0.mem.readLE (BitVec.ofNat 64 IfaceModel.VAL).toNat 16)
    s'.regs 0 = ((AMap.empty : AMap (BitVec 128) (BitVec 64)) key).getD 0 ∧ (s'.regs 1).toNat % 256 = ((AMap.empty : AMap (BitVec 128) (BitVec 64)) key).isSome.toNat) :=
  correctness implAt (ME (BitVec 128)) (ME_laws _) hcon (BitVec.ofNat 64 MP) (BitVec.ofNat 64 IfaceModel.VAL) AMap.empty ret hret s0 setup pre

end Witness

end Proof
