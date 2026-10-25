import Extracted

/-!
# `int64_t e_tls_add(int64_t x)` (C, arm64): a `__thread` variable, general-dynamic model

```c
static __thread int64_t e_tls;                 /* -fPIC: general dynamic (TLSDESC) */
int64_t e_tls_add(int64_t x) { e_tls += x; return e_tls; }
```

**Guarantee.** For every `x`, every AAPCS64 call of the gcc-compiled `e_tls_add` on a thread
whose TLS block is in place (`TLSBlock`: the executable's block at `TPIDR_EL0 + 16`, writable),
with 16 bytes of stack below `SP` apart from the variable, returns without faulting, restores
the callee-saved state, returns `e_tls + x (mod 2^64)` and stores it in this thread's `e_tls`;
nothing else changes but the frame record below `SP`.

**How.** cgo compiles C with `-fPIC`, so gcc emits the general-dynamic TLSDESC sequence
(`adrp`/`ldr`/`add`/`blr` through the descriptor). In an executable the linker relaxes it to
local-exec: `movz`/`movk` of the variable's offset from the thread pointer and two `nop`s, then
`mrs x2, tpidr_el0` and the access at `x2 + x0`. The proof checks that the constant is the
address `TLSImage.a64Addr` computes from `PT_TLS` and the symbol (`Extracted.tls`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI Janus.Contracts.Libc

namespace Proof

/-- This thread's `e_tls`. -/
abbrev var (s : State) : Nat := Extracted.tls.a64Addr s.tpidr "e_tls"

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => TLSBlock Extracted.tls s ∧ CStack s 16 0 ∧ Outside (var s) 8 [(s.sp.toNat - 16, s.sp.toNat)])
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [(var s, var s + 8), (s.sp.toNat - 16, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨htb, hta⟩, ⟨hal, hb, ha, hw⟩, hout⟩
  janus_intro hs.call
  have e1 : Extracted.tls.a64Off = janus_eval% Extracted.tls.a64Off := rfl
  have e2 : Extracted.tls.varOff "e_tls" = janus_eval% (Extracted.tls.varOff "e_tls") := rfl
  have e3 : Extracted.tls.size = janus_eval% Extracted.tls.size := rfl
  simp only [var, TLSImage.a64Addr, e1, e2, e3] at hta htb hout ⊢
  simp only [outside_cons, outside_nil, and_true] at hout
  have hvacc : s.mem.accessible (s.tpidr.toNat + 16 + 16) 8 true = true :=
    Memory.accessible_mono _ hta (by omega) (by omega)
  janus_run
  rw [show s.tpidr.toNat + 16 + 16 = s.tpidr.toNat + 32 by omega]
  refine ⟨by omega, by omega, by janus_frame⟩

end Proof
