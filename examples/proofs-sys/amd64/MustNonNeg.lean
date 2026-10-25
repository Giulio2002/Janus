import Janus
import Extracted

/-!
# `MustNonNeg(x int64) int64`: returns `x`, or ends in a breakpoint trap (amd64)

The amd64 build of `examples/sys.MustNonNeg` (see the arm64 proof): `runtime.breakpoint` is
`INT3`, which gets a `.trap` stub; executed, it faults with `Fault.trap pc 5` (`SIGTRAP`).

* `correctness`: for `0 ≤ x` (signed) the call returns `x` in `RAX`;
* `traps`: for `x < 0` the run ends in the breakpoint trap.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Kernel Janus.Amd64.Kernel

namespace Proof

theorem msb_of_nonneg (x : BitVec 64) (hx : 0 ≤ x.toInt) : x.msb = false := by
  have h : x.toNat < 2 ^ 63 := by
    rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h | h
    · exact h
    · exact absurd ((BitVec.toInt_neg_iff (x := x)).mpr (by omega)) (by omega)
  rw [BitVec.msb_eq_decide]; simp; omega

theorem msb_of_neg (x : BitVec 64) (hx : x.toInt < 0) : x.msb = true := by
  have h : 2 ^ 63 ≤ x.toNat := by have := (BitVec.toInt_neg_iff (x := x)).mp hx; omega
  rw [BitVec.msb_eq_decide]; simp; omega

theorem correctness (x : BitVec 64) (hx : 0 ≤ x.toInt) :
    Ensures Extracted.program Extracted.entry [x] (fun s => StackGuardOK s 0 ∧ StackWritable s 16 16)
      (fun _ s' => s'.regs 0 = x) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hb, ha, hw⟩⟩
  have hm := msb_of_nonneg x hx
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw
  janus64_run [hm]

theorem traps (x : BitVec 64) (hx : x.toInt < 0) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s)
    (hg : StackGuardOK s 0) (hst : StackWritable s 16 16) :
    Janus.Amd64.Kernel.Traps (Extracted.program.withExit ret) s := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hb, ha, hw⟩ := hst
  have hm := msb_of_neg x hx
  janus64_intro hs
  simp only [regG, regSP, stackguard0Offset, stackguard0] at hg1 hg2 hg3 hb ha hw
  unfold Janus.Amd64.Kernel.Traps
  janus64_run [hm]
  rw [Janus.Amd64.Kernel.trapAt_withExit]
  decide

end Proof
