import Janus
import Extracted

/-!
# `Clamp(x, hi uint64) uint64` built with `-cover -covermode=count` (amd64)

```go
func Clamp(x, hi uint64) uint64 {
	if x > hi {
		return hi
	}
	return x
}
```

**Guarantee.** As on arm64: for all `x`, `hi` and every Go call state in which the function's
coverage counter block (`ctr`, 24 bytes of the package's counter variable) is writable and the
package-id variable (`pkgVar`) readable and apart from it and from the return-address slot, the call returns, obeys the ABI,
returns `min(x, hi)` in `RAX`, and leaves the counter block as `-covermode=count` defines it
(`Instrument.CovBlock`: header `(3, pkg id, 0)`, the entry block's counter and the counter of
the branch taken incremented once, wrapping at `2^32`). Nothing else in memory changes.

`ctr` and `pkgVar` are the RIP-relative operands of the first two instructions, recomputed from
the extracted bytes (writable globals the extractor does not copy).
-/

namespace Proof
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts.Instrument

/-- The function's counter block: the operand of `MOVL $3, ctr(IP)` at `Clamp+0x0`. -/
def ctr : Nat := ripTarget Extracted.program Extracted.entry

/-- The package-id variable `goCover_<hash>_P`: the operand of the `MOVL` at `Clamp+0xa`. -/
def pkgVar : Nat := ripTarget Extracted.program (Extracted.entry + 0xa)

/-- The blocks a call runs: the entry block (counter 0), then `return x` (counter 1) when
`x ≤ hi`, or the `if` body `return hi` (counter 2) when `x > hi`. -/
def ran (x hi : Nat) (i : Nat) : Bool := i == 0 || (i == 1 && x ≤ hi) || (i == 2 && hi < x)

theorem correctness (x hi : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, hi]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible ctr 24 true = true ∧ ctr + 24 ≤ 2 ^ 48 ∧
        s.mem.accessible pkgVar 4 false = true ∧ pkgVar + 4 ≤ 2 ^ 48 ∧ Spec.Disjoint pkgVar 4 ctr 24 ∧
        Spec.Disjoint ctr 24 (s.regs regSP).toNat 8)
      (fun s s' => (s'.regs 0).toNat = min x.toNat hi.toNat ∧
        CovBlock s'.mem ctr (s.mem.readLE pkgVar 4) 0
          (bumped [covWord s.mem ctr 3, covWord s.mem ctr 4, covWord s.mem ctr 5] (ran x.toNat hi.toNat)) ∧
        OnlyWrites s.mem s'.mem ctr 24) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, hc, hc', hp, hp', hd, hds⟩
  simp only [Spec.Disjoint] at hd hds
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  janus_eval_nat hC : ctr
  janus_eval_nat hP : pkgVar
  rw [hC] at hc hc' hd hds ⊢
  rw [hP] at hp hp' hd ⊢
  have h4 := Arm64.Memory.readLE_lt s.mem 5539052 4
  have hc3 := Arm64.Memory.readLE_lt s.mem 5626412 4
  have hc4 := Arm64.Memory.readLE_lt s.mem 5626416 4
  have hc5 := Arm64.Memory.readLE_lt s.mem 5626420 4
  have hlt : decide (hi.toNat < x.toNat) = !decide (x.toNat ≤ hi.toNat) := by
    by_cases h : x.toNat ≤ hi.toNat <;> simp [h] <;> omega
  janus64_run
  all_goals
    refine ⟨by omega, ?_, ?_⟩
    · rw [bumped3]
      simp only [ran, covWord, bump, Nat.reduceMul, Nat.reduceAdd]
      have hnb : ¬ hi.toNat < x.toNat ↔ x.toNat ≤ hi.toNat := Nat.not_lt
      simp only [hlt] 
      by_cases hxy : x.toNat ≤ hi.toNat <;> simp only [hxy, decide_true, decide_false, Bool.and_true,
        Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.or_true,
        Bool.true_or, Bool.false_eq_true, Nat.reduceBEq, ite_true, ite_false, reduceIte] <;> (try omega)
      apply CovBlock.mk3 <;> simp (disch := omega) only [covWord, Arm64.Memory.readLE_writeLE_self,
        Arm64.Memory.readLE_writeLE_of_disjoint, Nat.reduceMul, Nat.reduceAdd] <;> omega
    · simp (disch := omega) only [onlyWrites_writeLE_iff, onlyWrites_self]

end Proof
