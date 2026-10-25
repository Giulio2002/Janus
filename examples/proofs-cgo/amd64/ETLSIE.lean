import Extracted

/-!
# `int64_t e_tls_ie_add(int64_t x)` (C, amd64): a `__thread` variable, initial-exec model

```c
static __thread int64_t e_tls_ie __attribute__((tls_model("initial-exec")));
int64_t e_tls_ie_add(int64_t x) { e_tls_ie += x; return e_tls_ie; }
```

**Guarantee.** For every `x`, every System V call of the gcc-compiled `e_tls_ie_add` on a thread
whose TLS block is in place (`TLSBlock`), returns `e_tls_ie + x (mod 2^64)` and stores it in this
thread's `e_tls_ie`; memory changes nowhere else.

**How.** gcc emits `mov e_tls_ie@gottpoff(%rip), %rdx; mov %fs:(%rdx), %rax`; in an executable
the linker relaxes the GOT load to an immediate (`mov $-16, %rdx`), the variable's offset from
`FS` in variant II, checked against `TLSImage.x64Addr`.
-/

open Janus.Contracts.Libc (memFrame_trans)
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Contracts.LibcAmd64

namespace Proof

theorem memFrame_writeLE (m : Janus.Arm64.Memory) (a n v : Nat) : MemFrame m (m.writeLE a n v) [(a, a + n)] :=
  Janus.Contracts.Libc.memFrame_of_bytes rfl fun _ h => Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)

abbrev var (s : State) : Nat := Extracted.tls.x64Addr s.fsBase "e_tls_ie"

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => TLSBlock Extracted.tls s ∧ CStack s 0 8 ∧
        Outside (var s) 8 [((s.regs 4).toNat, (s.regs 4).toNat + 8)])
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [(var s, var s + 8)]) := by
  intro ret hret s hs ⟨⟨⟨hb1, hb2⟩, hblk, hsa, hsv⟩, ⟨_, hsb, hnw, hacc⟩, hout⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = x := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Amd64.Program.withExit] at hacc hnw h_ret hsb
  have e1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have e2 : Extracted.tls.varOff "e_tls_ie" = janus_eval% (Extracted.tls.varOff "e_tls_ie") := rfl
  simp only [var, TLSImage.x64Addr, e1, e2] at hblk hb1 hout ⊢
  simp only [outside_cons, outside_nil, and_true] at hout
  have hvacc : s.mem.accessible (s.fsBase.toNat - 24 + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hblk (by omega) (by omega)
  have hfs : (s.fsBase.toNat + 18446744073709551600) % 18446744073709551616 = s.fsBase.toNat - 24 + 8 := by omega
  have hfs' : (18446744073709551600 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 24 + 8 := by omega
  janus64_run
  rw [show s.fsBase.toNat - 24 + 8 = s.fsBase.toNat - 16 by omega]
  exact ⟨rfl, rfl, memFrame_writeLE _ _ _ _⟩

end Proof
