import Extracted

/-!
# `NewMap()` returns a new, empty, non-nil map (arm64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns a non-nil header pointer that represents the empty map (through `makemap_small`).

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

theorem correctness (impl : List Segment) (M : MapModel (BitVec 64) (BitVec 64)) (hl : M.Laws)
    (H : RtReady) (hmk : MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H) :
    Ensures (Extracted.program.link impl) Extracted.entry []
      (fun s => CallerOK M s 16 0 ∧ H [] (s.regs 28).toNat (s.sp.toNat - 16) (rtView M.priv s.mem))
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        M.Env s'.mem (s.regs 28)) := by
  intro ret hret s hs ⟨hc, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  janus_run until [Extracted.program.contractAddr "runtime.makemap_small"]
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg]) (by simp [setReg])
      (by decide) (by decide), ?_⟩ ?_
  · simp only [Ready, setReg_apply, reduceIte, Nat.reduceEqDiff]
    rw [rtView_writeLE (Outside.of_sub hout (by omega) (by omega)),
      rtView_writeLE (Outside.of_sub hout (by omega) (by omega)),
      show (s.sp - 16#64).toNat = s.sp.toNat - 16 by
        rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl]
    exact hH
  · intro s' hpc' ⟨r, vr, fl, m', hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil] at hfr
    janus_run
    simp only [setReg_apply, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' ⊢
    exact ⟨hnz, hrep, henv'⟩

end Proof
