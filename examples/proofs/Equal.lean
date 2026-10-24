import Extracted

/-!
# `Equal(a, b any) bool` compares two interface values (arm64)

**Guarantee.** For all interface values `a = (ta, pa)` and `b = (tb, pb)`, every model `R` of the
interface runtime satisfying its laws, every implementation of `runtime.efaceeq` satisfying the
`Efaceeq` contract and every Go call state with `R.depth` bytes of stack below `Equal`'s 48-byte
frame (`CallerOK`) in which, when the type words are equal, the values can be compared
(`EqOK`) and their comparison does not depend on the stack window `Equal` writes (`EqFrame`),
the call returns, obeys the ABI, and the low byte of the result is Go's `a == b`:

* `ta ≠ tb` (different dynamic types): `false`, without a runtime call;
* `ta = tb = 0` (both nil): `true`;
* otherwise `efaceeq`: for a direct-interface type the data words compare, else `R.eq ta`, the
  type's equality on the values at `pa` and `pb` at the call; for a `TFlagRegularMemory` type
  that is not direct (e.g. `uint64`, structs of integers), whose values are readable and outside
  the window, that is equality of their `Size_` bytes.

**Assumptions (all in the statement).** `R` is *any* model satisfying `R.Laws`; the code at
`runtime.efaceeq` is *any* code that behaves as `Efaceeq` says (docs/RUNTIME-CONTRACTS.md,
"Interfaces").
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Iface

namespace Proof

/-- The stack window `Equal` and the runtime write: `R.depth` bytes below the 48-byte frame, the
frame, and the four argument spill slots above `SP`. -/
def window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [(s.sp.toNat - (R.depth + 48), s.sp.toNat + 40)]

theorem correctness (impl : List Segment) (R : IfaceModel) (hl : R.Laws)
    (heq : Efaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.efaceeq") R)
    (ta pa tb pb : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [ta, pa, tb, pb]
      (fun s => CallerOK R s 48 40 ∧ (ta = tb →
        EqOK R s.mem ta.toNat pa.toNat pb.toNat ∧ EqFrame R ta.toNat s.mem pa.toNat pb.toNat (window R s)))
      (fun s s' => (s'.regs 0).toNat % 256 =
          (ta == tb && efaceEqual R s.mem ta.toNat pa.toNat pb.toNat).toNat ∧
        (ta = tb → ta ≠ 0 → isRegularMemory s.mem ta.toNat = true →
          isDirectIface s.mem ta.toNat = false →
          s.mem.accessible pa.toNat (tySize s.mem ta.toNat) false = true →
          s.mem.accessible pb.toNat (tySize s.mem ta.toNat) false = true →
          (s'.regs 0).toNat % 256 = (s.mem.readLE pa.toNat (tySize s.mem ta.toNat) ==
            s.mem.readLE pb.toNat (tySize s.mem ta.toNat)).toNat)) := by
  intro ret hret s hs ⟨hc, hok⟩
  have hc' := hc
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd8, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus_intro hs
  simp only [regG, stackguard0Offset, stackguard0, Disjoint] at hg1 hg2 hg3 hgd
  by_cases htt : ta = tb
  · subst htt
    obtain ⟨hok1, hok2⟩ := hok rfl
    janus_run until [Extracted.program.contractAddr "runtime.efaceeq"]
    refine Reaches.call (Summary.withExit heq hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp; omega) rfl (by simp [setReg])
        (by simp [setReg]) (by decide) (by decide), ?_⟩ ?_
    · simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x1]
      exact EqFrame.eqOK hok2 hok1 (by simp only [window]; janus_frame)
    · intro s' hpc' ⟨r, v, fl, m', hs', hfr, henv', hres⟩
      subst hs'
      simp only [rtWrites, calleeStack, List.append_nil] at hfr
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff, h_x0, h_x1] at hres
      rw [EqFrame.efaceEqual hok2 (by simp only [window]; janus_frame)] at hres
      janus_run
      refine ⟨by simpa [setReg] using hres, fun ht0 hreg hnd hx hy => ?_⟩
      rw [← efaceEqual_regular hl henv ht0 (hok1 ht0).1 hreg hnd hx hy]
      simpa [setReg] using hres
  · janus_run
    exact ⟨by simp [show (ta == tb) = false from beq_false_of_ne htt], fun h => absurd h htt⟩

end Proof
