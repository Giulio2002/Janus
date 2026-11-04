import Extracted

/-!
# `Lookup(m, k)` returns `m[k]` and whether `k` is present (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns (never faulting or panicking), obeys the ABI, and returns the value stored under `k` (`0` if absent, also for a nil map) and, in the low byte of the second result register, `1` iff `k` is present.

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
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.Lookup" 8)
    (segWord Extracted.program "example.com/basic.Lookup" 9) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hacc : Access2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_fast64") M)
    (m k : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k]
      (fun s => CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem m.toNat f)
      (fun _ s' => s'.regs 0 = (f k).getD 0 ∧ (s'.regs 1).toNat % 256 = (f k).isSome.toNat) := by
  intro ret hret s hs ⟨hc, hty, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.mapaccess2_fast64"]
  refine Reaches.call (Summary.withExit (hacc f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
     by simpa [setReg] using hty, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact IsMap.frame hl hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48)) (hi := s.sp.toNat + 0)
      (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hoth, hmap', ⟨hs1, hs2, hs3⟩, hok⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    have hacc0 : s.mem.accessible (r 0).toNat 8 false = true := by
      rw [← hs1, hfr.accessible]; simp
    janus_run
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hs3 hok
    exact ⟨by rw [hs3]; simp, hok⟩

/-! ## Non-vacuity witness

The stub `Janus/Contracts/LiveStubMap.lean` `accessSeg` sits at `runtime.mapaccess2_fast64`'s address
in this program; `janus_map_access2` proves `Access2` for it (the model `ME`: one empty non-nil map)
by running the stub code. Below, a concrete call state of `Lookup(map, 5)` satisfies the whole
precondition and the call returns what the theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSat Janus.Contracts.LiveStubMap
open Janus.Contracts.IfaceModel (wsp wg)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapaccess2_fast64"))
theorem addr : Extracted.program.contractAddr "runtime.mapaccess2_fast64" = cA := by decide
def implAt : List Segment := [accessSeg cA]
def linked : Program := Extracted.program.link implAt

theorem hacc0 : Access2 linked cA (ME (BitVec 64)) := by janus_map_access2

theorem hacc : Access2 (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapaccess2_fast64") (ME (BitVec 64)) := by
  rw [addr]; exact hacc0

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Memory := withData mmem dat
def ret : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 1 then 5 else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (ME (BitVec 64)) s0 48 0 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  · simp only [ME_priv, ME_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Disjoint, ME_depth]; decide
  · simp only [ME_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (ME (BitVec 64)) s0 48 0 ∧ (ME (BitVec 64)).Typ mapType ∧
    IsMap (ME (BitVec 64)) s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty :=
  ⟨callerOK, trivial, (isMap_of_ne (by decide)).2 ⟨rfl, rfl, by decide, by decide⟩⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapaccess2_fast64`
meeting `Access2` for it, and a call state of `Lookup(map, 5)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (ret : Nat)
    (s : State), M.Laws ∧
    Access2 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess2_fast64") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5] s ∧
    (CallerOK M s 48 0 ∧ M.Typ mapType ∧ IsMap M s.mem (BitVec.ofNat 64 MP).toNat AMap.empty) :=
  ⟨implAt, ME _, ret, s0, ME_laws _, hacc, hret, setup, pre⟩

/-- The theorem fires: `Lookup(map, 5)` on the empty map returns `0` and `false`. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 0 = (emp 5).getD 0 ∧
      (s'.regs 1).toNat % 256 = (emp 5).isSome.toNat) :=
  correctness implAt (ME _) (ME_laws _) hacc (BitVec.ofNat 64 MP) 5 emp ret hret s0 setup pre

end Witness

end Proof
