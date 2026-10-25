import Extracted

/-!
# `IterSum(n int) uint64`: range over a function iterator (inlined, no runtime support)

**Guarantee.** For every 64-bit `n`, read as a signed `int`, and every Go call state of
`example.com/basic.IterSum`, the call returns (never faulting or panicking), obeys the ABI, and
`X0 = (0 + 1 + … + (N-1)) mod 2^64 = N·(N-1)/2 mod 2^64` where `N = max(n, 0)`: the iterator
`upTo(n)` yields `0, 1, …, n-1`.

**How.** The compiler inlines `upTo`, its closure and the loop body (the `yield` callback), and
removes the range-over-func state checks, so the compiled code is a plain counting loop with
no call to `runtime.panicrangestate` or any other runtime function. Its head is `cmp x1, x0;
b.gt` (signed; `i` in `X1`, the sum in `X2`); `loop` is the invariant there, proved by induction
on the `N - i` iterations left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- The loop head `cmp x1, x0`. -/
abbrev head : Nat := Extracted.entry + 0x1c

/-- `(i+1)·i/2 = i(i-1)/2 + i`. -/
theorem tri_succ (i : Nat) : (i + 1) * i / 2 = i * (i - 1) / 2 + i := by
  rcases i with _ | j
  · rfl
  · have : (j + 1 + 1) * (j + 1) = (j + 1) * (j + 1 - 1) + 2 * (j + 1) := by
      simp only [Nat.add_sub_cancel]; janus_ring
    rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem toInt_of_lt (i : BitVec 64) (h : i.toNat < 2 ^ 63) : i.toInt = i.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

theorem loop (n : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State) :
    ∀ k (S : State) (i acc : BitVec 64), i.toNat + k = n.toInt.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = n → S.regs 1 = i → S.regs 2 = acc →
      acc.toNat = i.toNat * (i.toNat - 1) / 2 % 2 ^ 64 →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = s.sp → S.regs 28 = s.regs 28 →
      S.regs 29 = s.regs 29 → S.regs 18 = s.regs 18 →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = n.toInt.toNat * (n.toInt.toNat - 1) / 2 % 2 ^ 64) := by
  have hn := BitVec.toInt_lt (x := n)
  simp only [Nat.add_one_sub_one] at hn
  intro k
  induction k with
  | zero =>
    intro S i acc hk hpc h0 h1 h2 hacc h30 hsp h28 h29 h18
    have hi : i.toInt = i.toNat := toInt_of_lt i (by omega)
    janus_run
    rw [hacc, show i.toNat = n.toInt.toNat by omega]
  | succ k ih =>
    intro S i acc hk hpc h0 h1 h2 hacc h30 hsp h28 h29 h18
    have hi : i.toInt = i.toNat := toInt_of_lt i (by omega)
    janus_run until [head]
    apply ih _ (i + 1#64) (acc + i)
    all_goals janus_simp
    all_goals try omega
    rw [tri_succ]
    omega

theorem correctness (n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [n] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = n.toInt.toNat * (n.toInt.toNat - 1) / 2 % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run until [head]
  exact loop n ret hret s n.toInt.toNat _ 0#64 0#64 (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
