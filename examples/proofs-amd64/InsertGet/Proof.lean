import Janus
import Extracted

/-!
# `InsertGet(m, k, v)` stores `m[k] = v` and reads it back: the result is `v` (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, for a non-nil map holding `f`, the call returns `v`, and memory represents `f` with `k ↦ v`. It goes through two contracts: `mapassign_fast64` (and the store through the slot it returns), then `mapaccess1_fast64`.

**Assumptions (all in the statement).** `M` is *any* representation of maps in memory satisfying
the layout laws `M.Laws`, and the runtime code at the contract address(es) `impl` is *any* code
that behaves as the named contract(s) of `Janus.Contracts.MapAmd64` say (docs/RUNTIME-CONTRACTS.md,
"Maps"). `CallerOK M s frame above` asks for the runtime environment, `M.depth` bytes of stack
below the function's own frame (writable, above the stack guard, outside the runtime's private
memory `M.priv`) and `mapType` is the type descriptor the code passes, recomputed from the
extracted RIP-relative `LEA`.

The runtime must be ready for the allocating call (`H : RtReady`, assumed at entry for that call; without it the contract was unsatisfiable, finding R3-C1, `audit/maps/model/Unsat.lean`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapAmd64

namespace Proof

def mapType : Nat := ripTarget Extracted.program (Extracted.entry + 0x23)

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws)
    (H : Contracts.RtReady) (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M H)
    (hacc : Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 40 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f ∧
        H [mapType, m.toNat, k.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (Contracts.rtView M.priv s.mem))
      (fun _ s' => s'.regs 0 = v ∧ M.Rep s'.mem m.toNat (f.set k v)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty hH
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.mapassign_fast64"]
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
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
    simp only [setRegF, reduceIte, Nat.reduceEqDiff] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := Janus.InRanges.disjoint hin (Outside.of_sub hout (a := (s.regs 4).toNat - (M.depth + 40))
      (n := M.depth + 40 + 32) (by omega) (by omega))
    have hdg := Janus.InRanges.disjoint hin hgo
    janus64_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast64"]
    have ho40 : Outside ((s.regs 4).toNat - 40) 8 M.priv := Outside.of_sub hout (by omega) (by omega)
    refine Reaches.call (Summary.withExit (hacc (f.set k v)) hret) rfl
      ⟨RTPre.of_parts hc (by rw [hl.env_writeLE _ _ ho40]; simpa [setRegF, keepABI] using (hset v).2.1)
        (fun a n w => by simp only [Arm64.Memory.accessible_writeLE, hfr.accessible])
        (by rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
              Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hfr.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true]
              exact ⟨hgo, by omega, by omega⟩)]
            repeat rw [Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
        (by simp [setRegF, keepABI, hsp40]) (by simp [setRegF, keepABI]) (by simp [keepX15, hs.zero])
        (by simpa using hs.df) (by simp [setRegF, keepABI, hsp40, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide),
       by simpa [setRegF] using hty, ?_⟩ ?_
    · simp only [setRegF, keepABI_apply]; simp only [reduceIte, Nat.reduceEqDiff]
      exact (isMap_of_ne hm0).2 (by rw [hl.rep_writeLE _ _ _ ho40]; exact (hset v).1)
    · intro s'' hpc'' ⟨r2, x2, y2, fl2, m'', _, _, hs'', hfr2, henv2, hoth2, hmap2, ⟨hs1, hs2, hs3⟩⟩
      subst hs''
      simp only [rtWrites, calleeStack, List.append_nil, setRegF, keepABI_apply, reduceIte,
        Nat.reduceEqDiff, hsp40] at hfr2
      have hacc1 : s.mem.accessible (r2 0).toNat 8 false = true := by
        rw [hfr2.accessible] at hs1; simpa [hfr.accessible] using hs1
      janus64_run
      all_goals simp only [setRegF, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hs3 hmap2
      exact ⟨by simp, (isMap_of_ne hm0).1 hmap2⟩

/-! ## Non-vacuity witness

The stub of `Janus/Contracts/LiveStubMapAmd64.lean` sits at `runtime.mapassign_fast64`'s address in this program;
`janus64_map_assign` proves `Assign` for it, and the stub for `runtime.mapaccess1_fast64` (`janus64_map_access1mc`) proves `Access1` (the model `MC`: one map of at most one entry) by running the stub code. Below, a
concrete call state of `InsertGet(map, 5, 7)` satisfies the whole precondition and the call returns what the
theorem describes. -/

namespace Witness

open Janus.Contracts.MapModel0 Janus.Contracts.MapSatAmd64 Janus.Contracts.LiveStubMapAmd64
open Janus.Contracts.IfaceModel (wsp wg wret)

/-- The contract address, as a numeral (the executor needs concrete addresses). -/
local macro "cA" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapassign_fast64"))
theorem addr : Extracted.program.contractAddr "runtime.mapassign_fast64" = cA := by decide
/-- The address of `runtime.mapaccess1_fast64`. -/
local macro "cB" : term => `(janus_eval% (Extracted.program.contractAddr "runtime.mapaccess1_fast64"))
theorem addrB : Extracted.program.contractAddr "runtime.mapaccess1_fast64" = cB := by decide
def implAt : List Janus.Amd64.Segment := [assignSeg cA, access1McSeg cB]
def linked : Janus.Amd64.Program := Extracted.program.link implAt

theorem h0 : Assign linked cA (MC ck64) HAssign := by janus64_map_assign

theorem hcon : Assign (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapassign_fast64") (MC ck64) HAssign := by
  rw [addr]; exact h0

theorem hB0 : Access1 linked cB (MC ck64) := by janus64_map_access1mc

theorem hB : Access1 (Extracted.program.link implAt)
    (Extracted.program.contractAddr "runtime.mapaccess1_fast64") (MC ck64) := by
  rw [addrB]; exact hB0

def emp : AMap (BitVec 64) (BitVec 64) := AMap.empty

def dat : DataSegment := Extracted.data.head!
def mem0 : Janus.Arm64.Memory := Janus.Contracts.LiveStubMap.withData mmem64 dat

def ret : Nat := wret

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 MP else if i = 3 then 5 else if i = 1 then 7 else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5, 7] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem callerOK : CallerOK (MC ck64) s0 40 32 := by
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp only [MC_priv, MC_depth, priv0, outside_cons, outside_nil, and_true]; decide
  · simp only [Janus.Spec.Disjoint, MC_depth]; decide
  · simp only [MC_priv, priv0, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem pre : CallerOK (MC ck64) s0 40 32 ∧ (MC ck64).Typ mapType ∧ (BitVec.ofNat 64 MP).toNat ≠ 0 ∧ (MC ck64).Rep s0.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    HAssign [mapType, (BitVec.ofNat 64 MP).toNat, (5 : BitVec 64).toNat] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (Contracts.rtView (MC ck64).priv s0.mem) :=
  ⟨callerOK, trivial, by decide, ⟨rfl, by decide, by decide, Or.inl ⟨by decide, rfl⟩⟩, by unfold HAssign; decide⟩

/-- The hypotheses are satisfiable: a model, an implementation of `runtime.mapassign_fast64`
meeting `Assign` for it, and a call state of `InsertGet(map, 5, 7)` that satisfies the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64)) (H : Contracts.RtReady) (ret : Nat)
    (s : Janus.Amd64.State), M.Laws ∧
    Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M H ∧
    Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [BitVec.ofNat 64 MP, 5, 7] s ∧
    (CallerOK M s 40 32 ∧ M.Typ mapType ∧ (BitVec.ofNat 64 MP).toNat ≠ 0 ∧ M.Rep s.mem (BitVec.ofNat 64 MP).toNat AMap.empty ∧
    H [mapType, (BitVec.ofNat 64 MP).toNat, (5 : BitVec 64).toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (Contracts.rtView M.priv s.mem)) :=
  ⟨implAt, (MC ck64), HAssign, ret, s0, (MC_laws _), hcon, hB, hret, setup, pre⟩

/-- The theorem fires: `InsertGet(map, 5, 7)` returns what the theorem says. -/
theorem returns : Returns ((Extracted.program.link implAt).withExit ret) s0 fun s' => ABIReturn s0 s' ∧
    (s'.regs 0 = 7 ∧ (MC ck64).Rep s'.mem (BitVec.ofNat 64 MP).toNat (emp.set 5 7)) :=
  correctness implAt (MC ck64) (MC_laws _) HAssign hcon hB (BitVec.ofNat 64 MP) 5 7 AMap.empty ret hret s0 setup pre

end Witness

end Proof
