import Janus
import Extracted

/-! `example.com/basic.Mul64` on amd64 (`MULQ BX; MOVQ AX, BX; MOVQ DX, AX; RET`): the full 128-bit product `(hi, lo)`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ hi lo, r = [hi, lo] ∧ hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * y.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  have hp : x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' x.isLt y.isLt
  generalize x.toNat * y.toNat = p at hp ⊢
  simp only [BitVec.toNat_ofNat]
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 3#64
def y : BitVec 64 := 4#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ hi lo, (results 2 s') = [hi, lo] ∧ hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * y.toNat) :=
  ⟨ret, s0, x, y, hret, setup, hpre, correctness x y ret hret s0 setup hpre⟩

end Witness

end Proof
