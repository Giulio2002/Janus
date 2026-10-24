import Janus
import Extracted

/-!
# `Equal(a, b any) bool` compares two interface values (amd64)

**Guarantee.** As the arm64 theorem (`examples/proofs/Equal.lean`), for the amd64 code: for all
interface values `a = (ta, pa)` (`RAX`, `RBX`) and `b = (tb, pb)` (`RCX`, `RDI`), every model `R`
satisfying its laws, every implementation of `runtime.efaceeq` satisfying `Efaceeq`
(`Janus/Contracts/IfaceAmd64.lean`) and every Go call state with `R.depth` bytes of stack below
`Equal`'s frame in which, when the type words are equal, the values can be compared and their
comparison does not depend on the stack window `Equal` writes, the call returns, obeys the ABI,
and `AL` is Go's `a == b`: `false` for different type words, `true` for two nils, otherwise
`efaceeq`'s answer, which for a `TFlagRegularMemory` type that is not direct is equality of the
`Size_` bytes of the values.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Proof

/-- The stack window `Equal` and the runtime write: `R.depth` bytes below the frame (with the
pushed return address), the frame, the return-address slot and the four spill slots. -/
def window (R : IfaceModel) (s : State) : List (Nat × Nat) :=
  [((s.regs 4).toNat - (R.depth + 40), (s.regs 4).toNat + 40)]

theorem correctness (impl : List Janus.Amd64.Segment) (R : IfaceModel) (hl : R.Laws)
    (heq : Efaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.efaceeq") R)
    (ta pa tb pb : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [ta, pa, tb, pb]
      (fun s => CallerOK R s 40 40 ∧ (ta = tb →
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
  obtain ⟨henv, ⟨hg1, hg2, hg3⟩, hal, hd, hb, hst, hout, hgd, hgo⟩ := hc'
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0, Janus.Spec.Disjoint] at hg1 hg2 hg3 hgd hgo hal hd hb hst hout
  have hsp40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp; omega
  by_cases htt : ta = tb
  · subst htt
    obtain ⟨hok1, hok2⟩ := hok rfl
    janus64_run until [Extracted.program.contractAddr "runtime.efaceeq"]
    refine Reaches.call (Summary.withExit heq hret) rfl
      ⟨RTPre.of_caller hl hc (by janus_frame) (by simp [setRegF, hsp40]) (by simp [setRegF])
        (by simpa using hs.zero) (by simpa using hs.df)
        (by simp [setRegF, hsp40, Arm64.Memory.readLE_writeLE_self]) (by decide) (by decide), ?_⟩ ?_
    · simp only [setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a1, h_a3]
      exact EqFrame.eqOK hok2 hok1 (by simp only [window]; janus_frame)
    · intro s' hpc' ⟨r, x, y, fl, m', hs', hfr, henv', hres⟩
      subst hs'
      simp only [Contracts.IfaceAmd64.rtWrites, Contracts.MapAmd64.calleeStack, List.append_nil,
        setRegF, reduceIte, Nat.reduceEqDiff, hsp40] at hfr
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, h_a0, h_a1, h_a3] at hres
      rw [EqFrame.efaceEqual hok2 (by simp only [window]; janus_frame)] at hres
      janus64_run
      refine ⟨hres, fun ht0 hreg hnd hx hy => ?_⟩
      rw [← efaceEqual_regular hl henv ht0 (hok1 ht0).1 hreg hnd hx hy]
      exact hres
  · have htt' : ta.toNat ≠ tb.toNat := fun h => htt (BitVec.eq_of_toNat_eq h)
    janus64_run
    exact ⟨by simp [show (ta == tb) = false from beq_false_of_ne htt], fun h => absurd h htt⟩

end Proof
