import Extracted

/-!
# `Sum(xs []uint64) uint64` returns the sum of the elements modulo `2^64` (a loop)

**Guarantee.** For every slice header `(ptr, len, cap)` in `X0`–`X2` and every Go call state `s`
of `example.com/basic.Sum` such that `SP` is aligned and `[SP+8, SP+16)` is writable (the spill
slot the function stores `ptr` into), `len < 2^63` (Go lengths are non-negative `int`s), the
`8·len` bytes at `ptr` are readable and do not overlap that spill slot, the call returns, obeys
the ABI, and `X0 = (xs[0] + … + xs[len-1]) mod 2^64` where `xs[k]` is the 64-bit word at
`ptr + 8k` before the call. This holds for every length, so the loop terminates and has no
out-of-bounds access.

**How (the template for loops).** `loop` is the invariant at the loop head (`cmp x1, x2`):
after `i` iterations the accumulator `X3` holds the sum of the first `i` words; it is proved by
induction on the number of iterations left, executing one iteration symbolically per step
(`janus_run until [head]`) and re-establishing the invariant with `janus_simp`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of the loop head `cmp x1, x2`. -/
abbrev head : Nat := Extracted.entry + 0x1c

theorem loop (ptr len : BitVec 64) (s : State) (hlen : len.toNat < 2 ^ 63)
    (hp : s.mem.accessible ptr.toNat (8 * len.toNat) false = true)
    (hp' : ptr.toNat + 8 * len.toNat ≤ 2 ^ 64)
    (hd : ptr.toNat + 8 * len.toNat ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 16 ≤ ptr.toNat) :
    ∀ n (S : State) (i acc : BitVec 64), i.toNat + n = len.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = ptr → S.regs 1 = len → S.regs 2 = i →
      S.regs 3 = acc → acc.toNat = sumWords s.mem ptr.toNat i.toNat % 2 ^ 64 →
      S.regs 30 = 0#64 → S.sp = s.sp → S.regs 28 = s.regs 28 → S.regs 29 = s.regs 29 →
      S.regs 18 = s.regs 18 → S.mem = s.mem.writeLE (s.sp.toNat + 8) 8 ptr.toNat →
      Reaches Extracted.program S (IsReturn fun s' => ABIReturn s s' ∧
        (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) := by
  intro n
  induction n with
  | zero =>
    intro S i acc hn hpc h0 h1 h2 h3 hacc h30 hsp h28 h29 h18 hm
    janus_run
    rw [hacc, show i.toNat = len.toNat by omega]
  | succ n ih =>
    intro S i acc hn hpc h0 h1 h2 h3 hacc h30 hsp h28 h29 h18 hm
    janus_run until [head]
    apply ih _ (i + 1#64) (acc + BitVec.ofNat 64 (s.mem.readLE (ptr.toNat + 8 * i.toNat) 8))
    all_goals janus_simp [sumWords_succ]
    all_goals omega

theorem correctness (ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [ptr, len, cap]
      (fun s => StackOK s 0 16 ∧ len.toNat < 2 ^ 63 ∧ Ptr s.mem ptr (8 * len.toNat) false ∧
        Disjoint ptr.toNat (8 * len.toNat) (s.sp.toNat + 8) 8)
      (fun s s' => (s'.regs 0).toNat = sumWords s.mem ptr.toNat len.toNat % 2 ^ 64) := by
  intro s hs ⟨⟨hal, hb, ha, hst⟩, hlen, ⟨hp, hp'⟩, hd⟩
  janus_intro hs
  simp only [Disjoint] at hd
  janus_run until [head]
  exact loop ptr len s hlen hp hp' hd len.toNat _ 0#64 0#64 (by simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by simp) (by janus_simp)
    (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp) (by janus_simp)

end Proof
