import Extracted

/-!
# Benchmark `Nested(n, m)` on arm64: a doubly nested loop

```go
for i := uint64(0); i < n; i++ { for j := uint64(0); j < m; j++ { s += i*m + j } }
```

returns `Σ_{i<n} Σ_{j<m} (i·m + j)` modulo `2^64` (`outerSum`), for all `n`, `m`.

**How.** Nested induction: the outer invariant (at the outer loop head, by induction on the
outer iterations left) is proved by running the outer prologue up to the inner head, and then
an inner induction whose base case runs back to the outer head and applies the outer
induction hypothesis. `janus_run until [outer, inner]` stops at either head.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The loop heads (`cmp x0, x2` and `cmp x1, x4`), relative to the entry. -/
abbrev outerHead : Nat := Extracted.entry + 0x10
abbrev innerHead : Nat := Extracted.entry + 0x2c

/-- `Σ_{j<k} (i·m + j)` -/
def innerSum (i m : W64) : Nat → W64
  | 0 => 0
  | k + 1 => innerSum i m k + (i * m + BitVec.ofNat 64 k)

/-- `Σ_{i<k} Σ_{j<m} (i·m + j)` -/
def outerSum (m : W64) : Nat → W64
  | 0 => 0
  | k + 1 => outerSum m k + innerSum (BitVec.ofNat 64 k) m m.toNat

theorem loops (n m : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State) :
    ∀ r i (S : State), i + r = n.toNat →
      S.pc = BitVec.ofNat 64 outerHead → S.regs 0 = n → S.regs 1 = m →
      S.regs 2 = BitVec.ofNat 64 i → S.regs 3 = outerSum m i →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 18 = s.regs 18 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.regs 29 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.regs 0 = outerSum m n.toNat) := by
  intro r
  induction r with
  | zero =>
    intro i S hi hpc h0 h1 h2 h3 h30 hsp h18 h28 h29
    have hi' : i < 2 ^ 64 := by omega
    janus_run
    subst hi; rfl
  | succ r ih =>
    intro i S hi hpc h0 h1 h2 h3 h30 hsp h18 h28 h29
    have hi' : i + 1 < 2 ^ 64 := by omega
    janus_run until [outerHead, innerHead]
    -- the inner loop, by induction on its iterations left
    suffices hin : ∀ q k (T : State), k + q = m.toNat →
        T.pc = BitVec.ofNat 64 innerHead → T.regs 0 = n → T.regs 1 = m →
        T.regs 2 = BitVec.ofNat 64 i → T.regs 4 = BitVec.ofNat 64 k →
        T.regs 3 = outerSum m i + innerSum (BitVec.ofNat 64 i) m k →
        T.regs 30 = BitVec.ofNat 64 ret → T.sp = s.sp → T.regs 18 = s.regs 18 →
        T.regs 28 = s.regs 28 → T.regs 29 = s.regs 29 →
        Reaches (Extracted.program.withExit ret) T (IsReturn fun s' => ABIReturn s s' ∧
          s'.regs 0 = outerSum m n.toNat) by
      apply hin m.toNat 0 _ (by omega)
      all_goals janus_simp [innerSum]
    intro q
    induction q with
    | zero =>
      intro k T hk tpc t0 t1 t2 t4 t3 t30 tsp t18 t28 t29
      janus_run until [outerHead, innerHead]
      apply ih (i + 1) _ (by omega)
      all_goals janus_simp [outerSum]
      all_goals first | rfl | rw [BitVec.ofNat_add] | rw [show k = m.toNat by omega]
    | succ q ihq =>
      intro k T hk tpc t0 t1 t2 t4 t3 t30 tsp t18 t28 t29
      have hk' : k + 1 < 2 ^ 64 := by omega
      janus_run until [outerHead, innerHead]
      apply ihq (k + 1) _ (by omega)
      all_goals janus_simp [innerSum]
      all_goals first | ac_rfl | rw [BitVec.ofNat_add]

theorem correctness (n m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n, m] (fun _ => True)
      (fun _ s' => s'.regs 0 = outerSum m n.toNat) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run until [outerHead]
  exact loops n m ret hret s n.toNat 0 _ (by omega) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp [outerSum]) (by janus_simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
