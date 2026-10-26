import Janus
import Extracted

/-!
# `NewMap()` returns a new, empty, non-nil map (amd64)

**Guarantee.** For every map value `m` holding the abstract map `f` (`IsMap`: nil and empty,
or represented by `M`) and every Go call state satisfying the precondition, the call returns a non-nil header pointer that represents the empty map (through `makemap_small`).

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

theorem correctness (impl : List Janus.Amd64.Segment) (M : MapModel (BitVec 64) (BitVec 64))
    (hl : M.Laws) (H : Contracts.RtReady)
    (hmk : MakeSmall (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makemap_small") M H) :
    Ensures (Extracted.program.link impl) Extracted.entry []
      (fun s => CallerOK M s 16 8 ∧
        H [] (s.regs 14).toNat ((s.regs 4).toNat - 16) (Contracts.rtView M.priv s.mem))
      (fun s s' => (s'.regs 0).toNat ≠ 0 ∧ M.Rep s'.mem (s'.regs 0).toNat AMap.empty ∧
        M.Env s'.mem (s.regs 14)) := by
  intro ret hret s hs ⟨hc, hH⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp16 : (s.regs 4 - 16#64).toNat = (s.regs 4).toNat - 16 := by
    rw [BitVec.toNat_sub]; simp; omega
  janus64_run until [Extracted.program.contractAddr "runtime.makemap_small"]
  refine Reaches.call (Summary.withExit hmk hret) rfl
    ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp16]) (by simp [setRegF])
      (by simpa using hs.zero) (by simpa using hs.df) (by simp [setRegF, keepABI, hsp16, Arm64.Memory.readLE_writeLE_self])
        (by decide) (by decide), ?_⟩ ?_
  · simp only [Contracts.Ready64, setRegF, reduceIte, Nat.reduceEqDiff, hsp16]
    repeat rw [Contracts.rtView_writeLE (Outside.of_sub hout (by omega) (by omega))]
    exact hH
  · intro s' hpc' ⟨r, x, y, fl, m', _, _, hs', hfr, henv', hoth, hnz, hrep, hfresh⟩
    subst hs'
    simp only [rtWrites, calleeStack, List.append_nil, setRegF, reduceIte, Nat.reduceEqDiff, hsp16] at hfr
    janus64_run
    simp only [setRegF, keepABI_apply, reduceIte, Nat.reduceEqDiff] at hnz hrep henv' ⊢
    exact ⟨hnz, hrep, henv'⟩

end Proof
