import Extracted

/-!
# `SumBelow(n int) uint64`: range over an integer

**Guarantee.** For every 64-bit `n`, read as a signed `int`, and every Go call state of
`example.com/basic.SumBelow`, the call returns (never faulting or panicking), obeys the ABI, and
`X0 = (0 + 1 + … + (N-1)) mod 2^64 = N·(N-1)/2 mod 2^64` where `N = max(n, 0)`: `for i := range n`
runs `n` times for positive `n` and not at all for `n ≤ 0`.

**How.** The loop head is `cmp x1, x0; b.gt` (a signed comparison, `i` in `X1`, the sum in `X2`).
`loop` is the invariant there, proved by induction on the `N - i` iterations left.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Proof

/-- The loop head `cmp x1, x0`. -/
abbrev head : Nat := Extracted.entry + 0x14

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


namespace Witness

def ret : Nat := 0x1000

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def sp0 : Nat := 0x108000
def g0 : Nat := 0x200000
def hp : Nat := 0x300000

def wbytes (a : Nat) : Byte := 0

def wmem : Memory := ⟨wbytes, [⟨sp0 - 0x8000, 0x10000, true⟩, ⟨g0, 0x100, false⟩, ⟨hp, 0x10000, true⟩]⟩


def s0 : State :=
  { regs := fun i => if i = 0 then (5) else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 (sp0 - 8)
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [(5 : BitVec 64)] s0 :=
  ⟨rfl, rfl, by
    intro i h
    simp only [List.length_cons, List.length_nil] at h
    have : i = 0 := by omega
    subst this; rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- All hypotheses of `correctness` hold together at a concrete call. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [n] s ∧ (True) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
      ABIReturn s s' ∧ ((s'.regs 0).toNat = n.toInt.toNat * (n.toInt.toNat - 1) / 2 % 2 ^ 64)) := by
  refine ⟨ret, s0, (5), hret, setup, ?pre, correctness (5) ret hret s0 setup ?pre⟩
  case pre =>
    try simp only [Janus.Spec.GuardOK, Janus.Spec.StackOK, Janus.Spec.Ptr, Janus.Spec.Ptr32, Janus.Spec.Disjoint, Janus.Spec.Aliasing, Janus.GoABI.FPConvention, Janus.Program.DataLoaded, Janus.Arm64.State.getV, s0, wmem, wbytes, sp0, g0, hp]
    all_goals decide

end Witness

end Proof
