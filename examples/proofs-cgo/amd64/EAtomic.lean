import Extracted

/-!
# `uint32_t e_atomic_inc(uint32_t *p)` (C, amd64): an atomic read-modify-write

```c
uint32_t e_atomic_inc(uint32_t *p) { return __atomic_add_fetch(p, 1, __ATOMIC_ACQ_REL); }
```

**Guarantee.** For every `p` (4-aligned, writable), every System V call of the gcc-compiled
`e_atomic_inc` returns `*p + 1 (mod 2^32)` in `EAX` and stores it at `p`; memory changes nowhere
else.

**How.** gcc inlines the atomic as `mov $1, %eax; lock xadd %eax, (%rdi); add $1, %eax` (no
outline helper on x86-64); the model runs `LOCK XADD` as one atomic exchange-and-add.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

theorem correctness (p : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p]
      (fun s => p.toNat % 4 = 0 ∧ p.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 4 true = true ∧
        CStack s 0 8 ∧ Outside p.toNat 4 [((s.regs 4).toNat, (s.regs 4).toNat + 8)])
      (fun s s' => (s'.regs 0).toNat % 2 ^ 32 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        s'.mem.readLE p.toNat 4 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        MemFrame s.mem s'.mem [(p.toNat, p.toNat + 4)]) := by
  intro ret hret s hs ⟨hal4, hpb, hpw, ⟨_, hsb, hnw, hacc⟩, hout⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Amd64.Program.withExit] at hacc hnw h_ret hsb
  simp only [outside_cons, outside_nil, and_true] at hout
  janus64_run
  refine ⟨by omega, by omega, Janus.Contracts.Libc.memFrame_of_bytes rfl fun _ h =>
    Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)⟩

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def P : Nat := 0x100000  -- addr-ok: a chosen counter

def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩, ⟨P, 4, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then BitVec.ofNat 64 P else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [BitVec.ofNat 64 P] s0 :=
  ⟨rfl, by decide, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem pre : (BitVec.ofNat 64 P).toNat % 4 = 0 ∧ (BitVec.ofNat 64 P).toNat + 4 ≤ 2 ^ 48 ∧
    s0.mem.accessible (BitVec.ofNat 64 P).toNat 4 true = true ∧
    CStack s0 0 8 ∧ Outside (BitVec.ofNat 64 P).toNat 4 [((s0.regs 4).toNat, (s0.regs 4).toNat + 8)] := by
  refine ⟨by decide, by decide, by decide, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true]; decide

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (p : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [p] s ∧
    (p.toNat % 4 = 0 ∧ p.toNat + 4 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 4 true = true ∧
      CStack s 0 8 ∧ Outside p.toNat 4 [((s.regs 4).toNat, (s.regs 4).toNat + 8)]) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat % 2 ^ 32 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        s'.mem.readLE p.toNat 4 = (s.mem.readLE p.toNat 4 + 1) % 2 ^ 32 ∧
        MemFrame s.mem s'.mem [(p.toNat, p.toNat + 4)])) :=
  ⟨_, ret, s0, hret, call, pre, correctness _ ret hret s0 call pre⟩

end Witness

end Proof
