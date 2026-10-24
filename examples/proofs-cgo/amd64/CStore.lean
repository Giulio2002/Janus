import Extracted

/-!
# `void c_store(uint64_t *p, uint64_t v)` (C, amd64): `*p = v`

**Guarantee.** For every pointer `p` to 8 writable bytes (below `2^48`) that do not overlap the
return-address slot at `[RSP]`, and every value `v`, every System V call of the gcc-compiled
`c_store` (return address readable at `[RSP]`) returns without faulting, restores `RSP + 8`,
`RBX RBP R12–R15` and the direction flag, and the only change to memory is the word at `p`,
which becomes `v`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

theorem correctness (p v : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, v]
      (fun s => CStack s 0 8 ∧ p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true ∧
        Disjoint p 8 (s.regs 4) 8)
      (fun s s' => s'.mem = s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, hb, hp, hd⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = v := hs.reg (i := 1) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  simp only [Disjoint] at hd
  janus64_run

end Proof
