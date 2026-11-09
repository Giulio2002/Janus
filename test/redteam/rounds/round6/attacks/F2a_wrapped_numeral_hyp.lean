import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-! Round 6 F2a: a hypothesis `y ≠ 18446744073709551616` at `BitVec 64`. The literal is `2^64`,
so a reader takes the hypothesis as vacuous ("Div returns x / y for every y"), but `OfNat` on
`BitVec 64` wraps it to `0`: it is the real precondition `y ≠ 0` (Div panics on 0). The text
round-trips exactly (Lean reads it back the same way), so before round 6 it verified with the
literal printed as a plain decimal. Round 6 rejects out-of-range literals. -/
namespace Proof
theorem correctness (x y : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret)
    (s : State) (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s)
    (hg : GuardOK s 0) (hst : StackOK s 24 0) (hy : y ≠ 18446744073709551616) :
    Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧
      (s'.regs 0).toNat = x.toNat / y.toNat) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  have hy0 : y ≠ 0 := hy
  have hy' : y.toNat ≠ 0 := fun h => hy0 (BitVec.eq_of_toNat_eq h)
  janus_run [hy']
end Proof
