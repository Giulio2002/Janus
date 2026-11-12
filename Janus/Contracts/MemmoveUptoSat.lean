import Janus.Contracts.LiveSat
import Janus.Contracts.LiveStubMemmoveUpto

/-!
# The variable-size `memmove` stub is a witness for `MemmoveLive` (arm64, U-MEMMOVE-UPTO)

`LiveStub.memmoveUptoSeg` placed at `A0` of a program with no other code meets `MemmoveLive` for a runtime that serves
the requests `[q, p, k]`, `1 ≤ k ≤ 32` (and the call state of the fixed-size witness, `k = 8`, satisfies the precondition), so
a theorem assuming `R.ok memmove [q, p, k]` for several sizes `k` is not vacuous.
-/

namespace Janus.Contracts.MemmoveUptoSat

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub
open Janus.Contracts.AllocSat (toy A0 at0 link_at0)

def okUp : Nat → List Nat → Prop := fun a args => a = A0 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32

set_option maxHeartbeats 16000000 in
theorem upto_impl : MemmoveLive (toy.link (at0 (memmoveUptoCode 32))) A0 4096 (toyR tys0 okUp) := by
  rw [link_at0]
  janus_live_memmove_upto 32 (fun _ h => h.2)

theorem memmoveUpto_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemmoveLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      Mem.EqPre 4096 3 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) ∧
      Mem.Input s 4096 3 (s.regs 1).toNat (s.regs 2).toNat ∧
      LiveDest R L s 4096 3 (s.regs 0).toNat (s.regs 2).toNat := by
  refine ⟨at0 (memmoveUptoCode 32), toyR tys0 okUp, upto_impl, [], 0x400, wst [CB, CB + 0x100, 8], rfl,
    wguardE _ 3 (by omega), ⟨⟨rfl, ⟨CB, CB + 0x100, 8, rfl, by decide, by decide⟩⟩, wmem_inv 0, by simp, wwin _ 3 (by omega)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide)⟩,
    ⟨by decide, by decide, cb_out_win _ 3 (by omega) _ _ (by decide), Or.inr (cb_out_rt _ _ (by decide))⟩⟩

/-! ### With `n = 0` (`MemmoveZeroLive`, `MemmoveLive.withZero`)

For `X2 = 0` the stub's compare chain falls through to its `RET`, so the same code meets `MemmoveZeroLive` for every runtime
hypothesis, and `MemmoveLive` for a runtime that also serves `n = 0` (`okUp0`, `0 ≤ k ≤ 32`). Both premises of
`MemmoveLive.withZero` hold of one implementation and one `R`, and its precondition holds at a call with `n = 0` and a
destination nothing is known about (`0`, a nil slice's pointer). -/

theorem upto_zero (d : Nat) (R : RtInv) : MemmoveZeroLive (toy.link (at0 (memmoveUptoCode 32))) A0 d R := by
  rw [link_at0]
  janus_live_memmove_zero

def okUp0 : Nat → List Nat → Prop := fun a args => a = A0 ∧ ∃ q p k, args = [q, p, k] ∧ k ≤ 32

theorem upto_impl0 : MemmoveLive (toy.link (at0 (memmoveUptoCode 32))) A0 4096 (toyR tys0 okUp0) := by
  intro L b s hpc pre
  by_cases h0 : (s.regs 2).toNat = 0
  · obtain ⟨k, s', hst, hr, hq⟩ := upto_zero 4096 (toyR tys0 okUp0) L b s hpc ⟨h0, pre.1, pre.2.1⟩
    exact ⟨k, s', hst, hr, LiveMemRet.of_nil hq fun _ i hi => absurd hi (by omega)⟩
  · obtain ⟨hE, ⟨⟨ha, q, p, k, hargs, hk⟩, hinv, hw1, hw2⟩, hI, hD⟩ := pre
    have hk1 : 1 ≤ k := by
      simp only [List.cons.injEq, and_true] at hargs; omega
    exact upto_impl L b s hpc ⟨hE, ⟨⟨ha, q, p, k, hargs, hk1, hk⟩, hinv, hw1, hw2⟩, hI, hD⟩

theorem memmoveUptoWithZero_satisfiable : ∃ (impl : List Segment) (R : RtInv),
    MemmoveLive (toy.link impl) A0 4096 R ∧ MemmoveZeroLive (toy.link impl) A0 4096 R ∧
    ∃ (L : List (Nat × Nat)) (b : Nat) (s : State), s.pc = BitVec.ofNat 64 A0 ∧
      (s.regs 0).toNat = 0 ∧ (s.regs 2).toNat = 0 ∧ Mem.EqPre 4096 3 s ∧
      LiveMemAt R A0 [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s 4096 3) := by
  refine ⟨at0 (memmoveUptoCode 32), toyR tys0 okUp0, upto_impl0, upto_zero 4096 _, [], 0x400, wst [0, CB + 0x100, 0], rfl,
    by decide, by decide, wguardE _ 3 (by omega), ⟨⟨rfl, ⟨0, CB + 0x100, 0, rfl, by decide⟩⟩, wmem_inv 0, by simp, wwin _ 3 (by omega)⟩⟩

end Janus.Contracts.MemmoveUptoSat
