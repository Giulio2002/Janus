import Extracted

/-!
# `GotoSum(n uint64) uint64`: a loop built from labels and `goto`

**Guarantee.** For every 64-bit `n` and every Go call state of `example.com/basic.GotoSum`, the
call returns (never faulting or panicking; so the `goto` loop terminates), obeys the ABI, and
`X0 = (1 + 2 + … + n) mod 2^64 = n·(n+1)/2 mod 2^64`.

**How.** The `goto loop` / `goto done` structure compiles to an ordinary loop whose head is
`cmp x1, x0` (`i` in `X1`, the sum in `X2`). `loop` is the invariant there: after `i` iterations
the sum is `i·(i+1)/2 mod 2^64`; it is proved by induction on the number `n - i` of iterations
left (the template of `Sum.lean`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- The loop head `cmp x1, x0`. -/
abbrev head : Nat := Extracted.entry + 0x18

/-- `(i+1)(i+2)/2 = i(i+1)/2 + (i+1)`. -/
theorem tri_succ (i : Nat) : (i + 1) * (i + 1 + 1) / 2 = i * (i + 1) / 2 + (i + 1) := by
  have : (i + 1) * (i + 1 + 1) = i * (i + 1) + 2 * (i + 1) := by janus_ring
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem loop (n : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + k = n.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = n → S.regs 1 = i → S.regs 2 = acc →
      acc.toNat = i.toNat * (i.toNat + 1) / 2 % 2 ^ 64 →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = n.toNat * (n.toNat + 1) / 2 % 2 ^ 64) := by
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc h0 h1 h2 hacc h30 hsp h28 h29 h18
    janus_run
    rw [hacc, show i.toNat = n.toNat by omega]
  | succ k ih =>
    intro S i acc hk hpc h0 h1 h2 hacc h30 hsp h28 h29 h18
    janus_run until [head]
    apply ih _ (i + 1#64) (i + acc + 1#64)
    all_goals janus_simp
    all_goals try omega
    rw [tri_succ]
    omega

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = n.toNat * (n.toNat + 1) / 2 % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run until [head]
  exact loop n ret hret s n.toNat _ 0#64 0#64 (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
