import Extracted

/-!
# `uint64_t c_add(uint64_t a, uint64_t b)` (C, amd64): returns `a + b`

**Guarantee.** For all 64-bit `a` and `b`, every System V call of the gcc-compiled `c_add` (any
admissible return address at `[RSP]`, `RSP + 8` 16-byte aligned, the 8 bytes of the return
address readable; every other register, the flags and memory arbitrary) returns after finitely
many steps without faulting, pops the return address, restores `RBX RBP R12–R15` and the
direction flag (`CReturn`), and leaves `(a + b) mod 2^64` in `RAX`.

The code is `endbr64; lea (%rdi,%rsi,1),%rax; ret`, copied from the cgo example binary.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

theorem correctness (a b : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, b] (fun s => CStack s 0 8)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨_, _, hnw, hacc⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = a := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = b := hs.reg (i := 1) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  janus64_run

end Proof
