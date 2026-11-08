import Extracted

/-!
# `int64_t e_tls_add(int64_t x)` (C, amd64): a `__thread` variable, general-dynamic model

```c
static __thread int64_t e_tls;                 /* -fPIC: general dynamic */
int64_t e_tls_add(int64_t x) { e_tls += x; return e_tls; }
```

**Guarantee.** For every `x`, every System V call of the gcc-compiled `e_tls_add` on a thread
whose TLS block is in place (`TLSBlock`: the executable's block just below `FS`, writable, and
the thread control block's self pointer at `FS:0`), with 8 bytes of stack below `RSP` apart
from the variable, returns `e_tls + x (mod 2^64)` and stores it in this thread's `e_tls`;
memory changes nowhere else but the saved `RBX` below `RSP`.

**How.** gcc emits the general-dynamic sequence (`data16 lea x@tlsgd(%rip), %rdi; data16 data16
rex.w call __tls_get_addr@PLT`); in an executable the linker relaxes it to local-exec:
`mov %fs:0, %rax` (the self pointer, padded to the same length with `data16` prefixes) and an
access at the variable's offset from it. The proof checks the offset against `TLSImage.x64Addr`.
-/

open Janus.Contracts.Libc (memFrame_trans)
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic Janus.Contracts.LibcAmd64

namespace Proof

theorem memFrame_writeLE (m : Janus.Arm64.Memory) (a n v : Nat) : MemFrame m (m.writeLE a n v) [(a, a + n)] :=
  Janus.Contracts.Libc.memFrame_of_bytes rfl fun _ h => Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)

abbrev var (s : State) : Nat := Extracted.tls.x64Addr s.fsBase "e_tls"

theorem correctness (x : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [x]
      (fun s => TLSBlock Extracted.tls s ∧ CStack s 8 8 ∧
        Outside (var s) 8 [((s.regs 4).toNat - 8, (s.regs 4).toNat + 8)] ∧
        Outside s.fsBase.toNat 8 [((s.regs 4).toNat - 8, (s.regs 4).toNat)])
      (fun s s' => (s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), (var s, var s + 8)]) := by
  intro ret hret s hs ⟨⟨⟨hb1, hb2⟩, hblk, hsa, hsv⟩, ⟨_, hsb, hnw, hacc⟩, hout, hout2⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = x := hs.reg (i := 0) (by simp)
  simp only [CABI.regSP, Amd64.Program.withExit] at hacc hnw h_ret hsb
  have e1 : Extracted.tls.x64Off = janus_eval% Extracted.tls.x64Off := rfl
  have e2 : Extracted.tls.varOff "e_tls" = janus_eval% (Extracted.tls.varOff "e_tls") := rfl
  simp only [var, TLSImage.x64Addr, e1, e2] at hblk hb1 hout ⊢
  simp only [outside_cons, outside_nil, and_true] at hout hout2
  have hself : (Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 3).toNat).readLE
      s.fsBase.toNat 8 = s.fsBase.toNat := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := s.mem) (a := (s.regs 4).toNat - 8) (n := 8) (b := s.fsBase.toNat) (k := 8) _ (by omega)]; exact hsv
  have hfs : (18446744073709551608 + s.fsBase.toNat) % 18446744073709551616 = s.fsBase.toNat - 8 := by omega
  have hvacc : s.mem.accessible (s.fsBase.toNat - 24 + 16) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hblk (by omega) (by omega)
  janus64_run
  rw [show s.fsBase.toNat - 24 + 16 = s.fsBase.toNat - 8 by omega]
  have h1 := memFrame_writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 3).toNat
  rw [show (s.regs 4).toNat - 8 + 8 = (s.regs 4).toNat by omega] at h1
  exact ⟨rfl, rfl, memFrame_trans (rs := [_]) (rs' := [_]) h1 (memFrame_writeLE _ _ _ _)⟩

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

theorem pre : TLSBlock Extracted.tls s0 ∧ CStack s0 8 8 ∧
    Outside (var s0) 8 [((s0.regs 4).toNat - 8, (s0.regs 4).toNat + 8)] ∧
    Outside s0.fsBase.toNat 8 [((s0.regs 4).toNat - 8, (s0.regs 4).toNat)] := by
  refine ⟨tls, ⟨by decide, by decide, by decide, by decide⟩, ?_, ?_⟩ <;>
  · simp only [outside_cons, outside_nil, and_true]; decide +kernel

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (x : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (TLSBlock Extracted.tls s ∧ CStack s 8 8 ∧
      Outside (var s) 8 [((s.regs 4).toNat - 8, (s.regs 4).toNat + 8)] ∧
      Outside s.fsBase.toNat 8 [((s.regs 4).toNat - 8, (s.regs 4).toNat)]) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      ((s'.regs 0).toNat = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        s'.mem.readLE (var s) 8 = (s.mem.readLE (var s) 8 + x.toNat) % 2 ^ 64 ∧
        MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), (var s, var s + 8)])) :=
  ⟨x0, ret, s0, hret, call, pre, correctness x0 ret hret s0 call pre⟩

end Witness

end Proof
