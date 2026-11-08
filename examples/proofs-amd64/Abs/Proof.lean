import Janus
import Extracted

/-!
# `Abs(x float64) float64` on amd64: clearing the sign bit

**Guarantee.** For every binary64 encoding `x` (NaNs included) and every Go call state of
`example.com/basic.Abs` with `x` in the low 64 bits of `X0`, the call returns, obeys the ABI,
and leaves in the low 64 bits of `X0` the encoding of `|x|`: `x` with its sign bit cleared
(`Janus.Float.abs`). Go compiles it to `MOVQ X0, AX; BTRQ $63, AX; MOVQ AX, X0`, so `MXCSR`
plays no part.
-/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry []
      (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat)
      (fun _ s' => (s'.xmm 0).toNat % 2 ^ 64 = abs binary64 x.toNat) := by
  intro ret hret s hs ⟨hst, hx⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hst
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run [hx]
  have hlt := x.isLt
  simp [abs, clearSign, binary64, Fmt.signBit]
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 0xBFF0000000000000#64

def s0 : State :=
  { regs := fun i => if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun i => if i = 0 then BitVec.ofNat 128 x.toNat else 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = x.toNat) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) , RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [] s ∧ (StackWritable s 0 8 ∧ (s.xmm 0).toNat % 2 ^ 64 = Witness.x.toNat) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ (s'.xmm 0).toNat % 2 ^ 64 = abs binary64 Witness.x.toNat) :=
  ⟨ret, s0, hret, setup, hpre, correctness x ret hret s0 setup hpre⟩

end Witness

end Proof
