import Extracted

/-!
# `Clamp(x, hi uint64) uint64` built with `-cover -covermode=count` (arm64)

```go
func Clamp(x, hi uint64) uint64 {
	if x > hi {
		return hi
	}
	return x
}
```

**Guarantee.** For all `x`, `hi` and every Go call state in which the function's coverage
counter block (`ctr`, 24 bytes of the package's counter variable) is writable and the package-id
variable (`pkgVar`) readable and apart from it, the call returns, obeys the ABI, returns
`min(x, hi)`, and leaves the counter block as `-covermode=count` defines it
(`Instrument.CovBlock`): the header `(3, pkg id, 0)` and the counters before the call with the
entry block's counter and the counter of the branch taken each incremented once (wrapping at
`2^32`). Nothing else in memory changes.

**Where the counters are.** `ctr` and `pkgVar` are the addresses the `ADRP`/`STR` and
`ADRP`/`LDR` pairs compute, recomputed from the extracted words; both are writable globals
(`.noptrbss`, `.noptrdata`) that the extractor does not copy, so the precondition states them.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Instrument

namespace Proof

/-- The function's counter block: the word `ADRP`+`STR` at `Clamp+0x4` writes (`ctr[0]`). -/
def ctr : Nat :=
  adrpLdTarget (Extracted.entry + 4) (segWord Extracted.program "example.com/rtmisc/cover.Clamp" 1)
    (segWord Extracted.program "example.com/rtmisc/cover.Clamp" 2) 2

/-- The package-id variable `goCover_<hash>_P`: the word `ADRP`+`LDR` at `Clamp+0xc` reads. -/
def pkgVar : Nat :=
  adrpLdTarget (Extracted.entry + 0xc) (segWord Extracted.program "example.com/rtmisc/cover.Clamp" 3)
    (segWord Extracted.program "example.com/rtmisc/cover.Clamp" 4) 2

/-- The blocks a call runs: the entry block (counter 0), then `return x` (counter 1) when
`x ≤ hi`, or the `if` body `return hi` (counter 2) when `x > hi`. -/
def ran (x hi : Nat) (i : Nat) : Bool := i == 0 || (i == 1 && x ≤ hi) || (i == 2 && hi < x)

theorem correctness (x hi : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, hi]
      (fun s => s.mem.accessible ctr 24 true = true ∧ ctr + 24 ≤ 2 ^ 48 ∧
        s.mem.accessible pkgVar 4 false = true ∧ pkgVar + 4 ≤ 2 ^ 48 ∧ Disjoint pkgVar 4 ctr 24)
      (fun s s' => (s'.regs 0).toNat = min x.toNat hi.toNat ∧
        CovBlock s'.mem ctr (s.mem.readLE pkgVar 4) 0
          (bumped [covWord s.mem ctr 3, covWord s.mem ctr 4, covWord s.mem ctr 5] (ran x.toNat hi.toNat)) ∧
        OnlyWrites s.mem s'.mem ctr 24) := by
  intro ret hret s hs ⟨hc, hc', hp, hp', hd⟩
  simp only [Disjoint] at hd
  janus_intro hs
  janus_eval_nat hC : ctr
  janus_eval_nat hP : pkgVar
  rw [hC] at hc hc' hd ⊢
  rw [hP] at hp hp' hd ⊢
  janus_run
  all_goals
    have h4 := Memory.readLE_lt s.mem 1432196 4
    have hc3 := Memory.readLE_lt s.mem 1519980 4
    have hc4 := Memory.readLE_lt s.mem 1519984 4
    have hc5 := Memory.readLE_lt s.mem 1519988 4
    refine ⟨by omega, ?_⟩
    rw [bumped3]
    simp only [ran, covWord, bump, Nat.reduceMul, Nat.reduceAdd]
    have hlt : decide (hi.toNat < x.toNat) = !decide (x.toNat ≤ hi.toNat) := by
      by_cases h : x.toNat ≤ hi.toNat <;> simp [h] <;> omega
    simp only [hlt]
    by_cases hxy : x.toNat ≤ hi.toNat <;> simp only [hxy, decide_true, decide_false, Bool.and_true,
      Bool.and_false, Bool.or_false, Bool.false_or, Bool.not_true, Bool.not_false, Bool.or_true,
      Bool.true_or, Bool.false_eq_true, Nat.reduceBEq, ite_true, ite_false, reduceIte] <;> (try omega)
    apply CovBlock.mk3 <;> simp (disch := omega) only [covWord, Memory.readLE_writeLE_self,
      Memory.readLE_writeLE_of_disjoint, Nat.reduceMul, Nat.reduceAdd] <;> omega

end Proof
