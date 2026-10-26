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

end Proof
