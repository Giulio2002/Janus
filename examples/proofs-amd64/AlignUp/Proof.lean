import Janus
import Extracted

/-! `example.com/basic.AlignUp(p, a uintptr) uintptr` on amd64: `uintptr` arithmetic, rounding up
to a power of two.

For all 64-bit `p`, `a` with `a = 2^k` and `p + a ≤ 2^64` (the rounded-up value is
representable), the result `r = RAX` is the smallest multiple of `a` that is at least `p`:
`r mod a = 0`, `p ≤ r` and `r < p + a`. The code is `(p + a - 1) & -a` (two `LEAQ`, `NEGQ`,
`ANDQ`). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Masking with `2^64 - 2^k` clears the low `k` bits. -/
theorem and_high (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64) :
    x &&& (2 ^ 64 - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
  have e : 2 ^ 64 - 2 ^ k = (2 ^ (64 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : k ≤ i
  · rw [Nat.sub_add_cancel h1]
    by_cases h2 : i < 64
    · simp [h1, show i - k < 64 - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [h1]

/-- The value the code computes, `((p + a - 1) mod 2^64) &&& (-a mod 2^64)`, is the least
multiple of `a = 2^k` that is at least `p`. -/
theorem round_up (p a k : Nat) (ha : a = 2 ^ k) (hpa : p + a ≤ 2 ^ 64) :
    ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) % a = 0 ∧
      p ≤ ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) ∧
      ((18446744073709551615 + (a + p)) % 18446744073709551616 &&&
        (18446744073709551616 - a) % 18446744073709551616) < p + a := by
  have ha1 : 1 ≤ a := ha ▸ Nat.one_le_two_pow
  have hk : k ≤ 64 := by
    have : 2 ^ k ≤ 2 ^ 64 := by omega
    exact (Nat.pow_le_pow_iff_right (by decide)).1 this
  rw [show (18446744073709551615 + (a + p)) % 18446744073709551616 = a + p - 1 by omega,
    show (18446744073709551616 - a) % 18446744073709551616 = 2 ^ 64 - 2 ^ k by omega,
    and_high _ _ (by omega) hk, ← ha]
  have hd := Nat.div_add_mod (a + p - 1) a
  have hm := Nat.mod_lt (a + p - 1) (show 0 < a by omega)
  rw [Nat.mul_comm] at hd
  refine ⟨Nat.mul_mod_left _ _, ?_, ?_⟩ <;>
    generalize (a + p - 1) / a * a = r at * <;> generalize (a + p - 1) % a = m at * <;> omega

theorem correctness (p a : BitVec 64) (k : Nat) :
    EnsuresResults Extracted.program Extracted.entry [p, a] 1
      (fun s => StackWritable s 0 8 ∧ a.toNat = 2 ^ k ∧ p.toNat + a.toNat ≤ 2 ^ 64)
      (fun res => ∃ r, res = [r] ∧ r.toNat % a.toNat = 0 ∧ p.toNat ≤ r.toNat ∧
        r.toNat < p.toNat + a.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ha, hpa⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, rfl, ?_⟩
  have e : (a + p - 1#64 &&& 0#64 - a).toNat =
      (18446744073709551615 + (a.toNat + p.toNat)) % 18446744073709551616 &&&
        (18446744073709551616 - a.toNat) % 18446744073709551616 := by
    rw [BitVec.toNat_and]
    first
      | (with_reducible congr 1 <;> simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)
      | (congr 1 <;> simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega)
  rw [e]
  exact round_up p.toNat a.toNat k ha hpa

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def p : BitVec 64 := 16#64
def a : BitVec 64 := 8#64
def k : Nat := 3

def s0 : State :=
  { regs := fun i => if i = 0 then p else if i = 3 then a else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [p, a] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ a.toNat = 2 ^ k ∧ p.toNat + a.toNat ≤ 2 ^ 64) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (p : BitVec 64) (a : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [p, a] s ∧ (StackWritable s 0 8 ∧ a.toNat = 2 ^ Witness.k ∧ p.toNat + a.toNat ≤ 2 ^ 64) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∃ r, (results 1 s') = [r] ∧ r.toNat % a.toNat = 0 ∧ p.toNat ≤ r.toNat ∧
        r.toNat < p.toNat + a.toNat) :=
  ⟨ret, s0, p, a, hret, setup, hpre, correctness p a k ret hret s0 setup hpre⟩

end Witness

end Proof
