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

end Proof
