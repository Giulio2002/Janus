import Janus
import Extracted

/-! `example.com/basic.BitMerge(x, y, m)` on amd64: two bit-merge formulas, `&^`, `&`, `|`, `^`.

For all 64-bit `x`, `y`, `m`, both results are the merge of `x` and `y` under the mask `m`: for
every bit position `i < 64`, bit `i` of each result is bit `i` of `y` if bit `i` of `m` is set and
bit `i` of `x` otherwise. The first is computed as `(x &^ m) | (y & m)` (`NOTQ`, `ANDQ`, `ORQ`),
the second as `x ^ ((x ^ y) & m)` (`XORQ`, `ANDQ`, `XORQ`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Bit `i` of the merge of `x` and `y` under `m`. -/
def mergeBit (x y m : BitVec 64) (i : Nat) : Bool := if m.getLsbD i then y.getLsbD i else x.getLsbD i

theorem correctness (x y m : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y, m] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ a b, r = [a, b] ∧ ∀ i < 64, a.getLsbD i = mergeBit x y m i ∧
        b.getLsbD i = mergeBit x y m i) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  intro i hi
  simp only [mergeBit, BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or, BitVec.getElem_and,
    BitVec.getElem_xor, BitVec.getElem_not]
  generalize x[i] = a, y[i] = b, m[i] = c
  revert a b c; decide

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def x : BitVec 64 := 0xF0F0#64
def y : BitVec 64 := 0x1234#64
def m : BitVec 64 := 0xFF#64

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 3 then y else if i = 1 then m else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64) (y : BitVec 64) (m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x, y, m] s ∧ (StackWritable s 0 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ a b, (results 2 s') = [a, b] ∧ ∀ i < 64, a.getLsbD i = mergeBit x y m i ∧
        b.getLsbD i = mergeBit x y m i) :=
  ⟨ret, s0, x, y, m, hret, setup, hpre, correctness x y m ret hret s0 setup hpre⟩

end Witness

end Proof
