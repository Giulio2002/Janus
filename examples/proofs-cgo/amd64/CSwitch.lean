import Extracted

/-!
# `uint64_t c_switch(uint64_t k, uint64_t x)` (C, amd64): a CET jump table

```c
switch (k) {
case 0: return x + 1;   case 1: return x * 3;   case 2: return x ^ 0x55;  case 3: return x - 7;
case 4: return x << 2;  case 5: return x >> 1;  case 6: return ~x;        case 7: return x * x;
default: return k + x;
}
```

gcc -O2 (with Ubuntu's default `-fcf-protection`) compiles the switch to `cmp $7,%rdi; ja
default`, a table of eight 32-bit offsets in `.rodata` (`lea table(%rip),%rdx; movslq
(%rdx,%rdi,4),%rax; add %rdx,%rax`) and the CET dispatch `notrack jmp *%rax` (`3E FF E0`).

**Guarantee.** For all 64-bit `k` and `x`, every System V call of `c_switch` whose memory holds
the extracted read-only jump table (`DataLoaded`) returns without faulting, restores what the
C calling convention requires (`CReturn`) and leaves `cswitch k x` in `RAX`. The proof splits
on the eight in-range values of `k`; for each, the jump target is computed from the table.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

/-- The C function, case by case. -/
def cswitch (k x : BitVec 64) : BitVec 64 :=
  if k = 0 then x + 1 else if k = 1 then x * 3 else if k = 2 then x ^^^ 0x55
  else if k = 3 then x - 7 else if k = 4 then x <<< 2 else if k = 5 then x >>> 1
  else if k = 6 then ~~~x else if k = 7 then x * x else k + x

theorem correctness (k x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [k, x]
      (fun s => CStack s 0 8 ∧ Extracted.program.DataLoaded s.mem)
      (fun _ s' => s'.regs 0 = cswitch k x) := by
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, hd⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = k := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = x := hs.reg (i := 1) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  by_cases hk : k.toNat ≤ 7
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 8 ∧ k = BitVec.ofNat 64 j :=
      ⟨k.toNat, by omega, by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt k.isLt]⟩
    janus64_cases hj
    all_goals
      janus64_data hd
      set_option maxRecDepth 4000 in janus64_run
    all_goals simp [cswitch]
    -- `x * 3` became `lea (%rsi,%rsi,2)`
    bv_omega
  · janus64_data hd
    janus64_run
    have hne : ∀ j : BitVec 64, j.toNat ≤ 7 → k ≠ j := fun j hj h => by subst h; omega
    rw [cswitch, if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)),
      if_neg (hne 2 (by decide)), if_neg (hne 3 (by decide)), if_neg (hne 4 (by decide)),
      if_neg (hne 5 (by decide)), if_neg (hne 6 (by decide)), if_neg (hne 7 (by decide))]

end Proof
