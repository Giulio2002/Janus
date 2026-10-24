import Extracted

/-!
# `InsertGet(m, k, v)` stores `m[k] = v` and reads it back: the result is `v` (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, for a non-nil map holding `f`, the call returns `v`, and memory represents `f` with `k ↦ v`. It goes through two contracts: `mapassign_fast64` (and the store through the slot it returns), then `mapaccess1_fast64`.

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
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program "example.com/basic.InsertGet" 11)
    (segWord Extracted.program "example.com/basic.InsertGet" 12) 0

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (hasn : Assign (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapassign_fast64") M)
    (hacc : Access1 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mapaccess1_fast64") M)
    (m k v : BitVec 64) (f : AMap (BitVec 64) (BitVec 64)) :
    Ensures (Extracted.program.link impl) Extracted.entry [m, k, v]
      (fun s => CallerOK M s 48 32 ∧ M.Typ mapType ∧ m.toNat ≠ 0 ∧ M.Rep s.mem m.toNat f)
      (fun _ s' => s'.regs 0 = v ∧ M.Rep s'.mem m.toNat (f.set k v)) := by
  intro ret hret s hs ⟨hc, hty, hm0, hmap⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  janus_eval_nat hT : mapType
  rw [hT] at hty
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd hgo
  janus_run until [Extracted.program.contractAddr "runtime.mapassign_fast64"]
  refine Reaches.call (Summary.withExit (hasn f) hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), by simpa [setReg] using hty, by simpa [setReg] using hm0, ?_⟩ ?_
  · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
    exact hl.rep_frame _ _ _ _ hmap (Agrees.of_window (lo := s.sp.toNat - (M.depth + 48))
      (hi := s.sp.toNat + 32) (by janus_frame) (Outside.of_sub hout (by omega) (by omega)))
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hw, hin, hset⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    simp only [setReg_apply, reduceIte, Nat.reduceEqDiff] at hset
    have hacc0 : s.mem.accessible (r 0).toNat 8 true = true := by
      rw [hfr.accessible] at hw; simpa using hw
    have hdis := InRanges.disjoint hin (Outside.of_sub hout (a := s.sp.toNat - (M.depth + 48))
      (n := M.depth + 48 + 32) (by omega) (by omega))
    have hdg := InRanges.disjoint hin hgo
    janus_run until [Extracted.program.contractAddr "runtime.mapaccess1_fast64"]
    have hrep2 := (hset v).1
    refine Reaches.call (Summary.withExit (hacc (f.set k v)) hret) rfl
      ⟨RTPre.of_parts hc (by simpa [setReg, keepABI] using (hset v).2.1)
        (fun a n w => by simp only [Memory.accessible_writeLE, hfr.accessible])
        (by rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), hfr.readLE _ _ (by
              simp only [outside_append, outside_cons, outside_nil, and_true, BitVec.toNat_sub,
                BitVec.toNat_ofNat]
              exact ⟨hgo, by omega, by omega⟩)]
            repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)])
        (by simp; omega) (by simp [setReg, keepABI]) (by simp [setReg]) (by simp [setReg]) (by decide) (by decide),
       by simpa [setReg] using hty, ?_⟩ ?_
    · simp only [setReg_apply, keepABI_apply]; simp only [reduceIte, Nat.reduceEqDiff]
      exact (isMap_of_ne hm0).2 hrep2
    · intro s'' hpc'' ⟨r2, vr2, fl2, m'', hs'', hfr2, henv2, hoth2, hmap2, ⟨hs1, hs2, hs3⟩⟩
      subst hs''
      simp only [rtWrites, calleeStack, List.append_nil] at hfr2
      have hacc1 : s.mem.accessible (r2 0).toNat 8 false = true := by
        rw [hfr2.accessible] at hs1; simpa [hfr.accessible] using hs1
      janus_run
      simp only [setReg_apply, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hs3 hmap2
      refine ⟨by rw [hs3]; simp, (isMap_of_ne hm0).1 hmap2⟩

end Proof
