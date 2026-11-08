import Extracted

/-!
# `int64_t e_tls_ie_add(int64_t x)` (C, arm64): a `__thread` variable, initial-exec model

```c
static __thread int64_t e_tls_ie __attribute__((tls_model("initial-exec")));
int64_t e_tls_ie_add(int64_t x) { e_tls_ie += x; return e_tls_ie; }
```

**Guarantee.** For every `x`, every AAPCS64 call of the gcc-compiled `e_tls_ie_add` on a thread
whose TLS block is in place (`TLSBlock`), returns without faulting, restores the callee-saved
state, returns `e_tls_ie + x (mod 2^64)` and stores it in this thread's `e_tls_ie`; nothing else
changes.

**How.** gcc emits the initial-exec sequence (`adrp`/`ldr` of the variable's TP offset from the
GOT, `mrs x1, tpidr_el0`, the access at `x1 + offset`); in an executable the linker relaxes the
GOT load to `movz`/`movk` of the offset. The proof checks that the address is the one
`TLSImage.a64Addr` computes from `PT_TLS` and the symbol (`Extracted.tls`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic Janus.FFI Janus.Contracts.Libc

namespace Proof

/-- This thread's `e_tls_ie`. -/
abbrev var (s : State) : Nat := Extracted.tls.a64Addr s.tpidr "e_tls_ie"

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => TLSBlock Extracted.tls s)
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE (var s) 8 ((s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64)) := by
  intro ret hret s hs ⟨htb, hta⟩
  janus_intro hs.call
  have e1 : Extracted.tls.a64Off = janus_eval% Extracted.tls.a64Off := rfl
  have e2 : Extracted.tls.varOff "e_tls_ie" = janus_eval% (Extracted.tls.varOff "e_tls_ie") := rfl
  have e3 : Extracted.tls.size = janus_eval% Extracted.tls.size := rfl
  simp only [var, TLSImage.a64Addr, e1, e2, e3] at hta htb ⊢
  have hvacc : s.mem.accessible (s.tpidr.toNat + 16 + 24) 8 true = true :=
    Memory.accessible_mono _ hta (by omega) (by omega)
  janus_run
  rw [show s.tpidr.toNat + 16 + 24 = s.tpidr.toNat + 40 by omega, Nat.add_comm _ x.toNat]
  exact ⟨rfl, rfl, rfl⟩

namespace Witness

def RET : Nat := 0x1000
def SP0 : Nat := 0x300000
def TP : Nat := 0x500000
def x0 : BitVec 64 := 5#64

/-- This thread's TLS block, writable. -/
def s0 : State :=
  { regs := fun i => if i = 0 then x0 else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 SP0, pc := BitVec.ofNat 64 Extracted.entry, tpidr := BitVec.ofNat 64 TP,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨fun _ => 0, [⟨TP + Extracted.tls.a64Off, Extracted.tls.size, true⟩]⟩,
    exclPass := fun _ => true }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [x0] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩, by decide, by decide⟩

theorem pre : TLSBlock Extracted.tls s0 := ⟨by decide +kernel, by decide +kernel⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧ (TLSBlock Extracted.tls s) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem = s.mem.writeLE (var s) 8 ((s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64))) :=
  ⟨x0, RET, s0, hret, call, pre, correctness x0 RET hret s0 call pre⟩

end Witness

end Proof
