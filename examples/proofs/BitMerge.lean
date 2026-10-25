import Extracted

/-!
# `BitMerge(x, y, m uint64) (uint64, uint64)`: two bit-merge formulas, `&^`, `&`, `|`, `^`

**Guarantee.** For all 64-bit `x`, `y`, `m` and every Go call state of
`example.com/basic.BitMerge`, the call returns (never faulting or panicking), obeys the ABI, and
both results are the merge of `x` and `y` under the mask `m`: for every bit position `i < 64`,
bit `i` of `X0` and of `X1` is bit `i` of `y` if bit `i` of `m` is set and bit `i` of `x`
otherwise. `X0` is computed as `(x &^ m) | (y & m)` (`bic`, `and`, `orr`), `X1` as
`x ^ ((x ^ y) & m)` (`eor`, `and`, `eor`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- Bit `i` of the merge of `x` and `y` under `m`. -/
def mergeBit (x y m : BitVec 64) (i : Nat) : Bool := if m.getLsbD i then y.getLsbD i else x.getLsbD i

theorem correctness (x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y, m] (fun _ => True)
      (fun _ s' => ∀ i < 64, (s'.regs 0).getLsbD i = mergeBit x y m i ∧
        (s'.regs 1).getLsbD i = mergeBit x y m i) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  intro i hi
  simp only [mergeBit, BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or, BitVec.getElem_and,
    BitVec.getElem_xor, BitVec.getElem_not]
  generalize x[i] = a, y[i] = b, m[i] = c
  revert a b c; decide

end Proof
