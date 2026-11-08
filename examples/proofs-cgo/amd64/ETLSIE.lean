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

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def F : Nat := 0x500000  -- addr-ok: a chosen thread control block
def x0 : BitVec 64 := 5#64

/-- The stack (return address at `[wsp]`), this thread's TLS block below `FS` (writable) and the
thread control block whose first word holds `FS`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp))
    else if F ≤ a ∧ a < F + 8 then BitVec.ofNat 8 (F / 256 ^ (a - F)) else 0,
   [⟨wsp - 64, 128, true⟩, ⟨F - Extracted.tls.x64Off, Extracted.tls.x64Off, true⟩, ⟨F, 8, false⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then x0 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, fsBase := BitVec.ofNat 64 F, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [x0] s0 :=
  ⟨rfl, by decide, by decide, by intro i h; simp at h; subst h; rfl, by decide, rfl⟩

theorem tls : TLSBlock Extracted.tls s0 :=
  ⟨⟨by decide +kernel, by decide⟩, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem pre : TLSBlock Extracted.tls s0 ∧ CStack s0 0 8 ∧
    Outside (var s0) 8 [((s0.regs 4).toNat, (s0.regs 4).toNat + 8)] := by
  refine ⟨tls, ⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  simp only [outside_cons, outside_nil, and_true]; decide +kernel

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (TLSBlock Extracted.tls s ∧ CStack s 0 8 ∧
      Outside (var s) 8 [((s.regs 4).toNat, (s.regs 4).toNat + 8)]) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [(var s, var s + 8)])) :=
  ⟨x0, ret, s0, hret, call, pre, correctness x0 ret hret s0 call pre⟩

end Witness

end Proof
