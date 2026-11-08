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

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def D : Nat := 0x100000  -- addr-ok: a chosen data window
def a0 : BitVec 64 := 3#64
def b0 : BitVec 64 := 4#64

/-- The stack window `[wsp - 64, wsp + 64)` (writable); the return address at `[wsp]`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then a0 else if i = 6 then b0 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [a0, b0] s0 :=
  ⟨rfl, by decide, by decide, by intro i h; simp only [List.length_cons, List.length_nil] at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, by decide, rfl⟩

theorem pre : CStack s0 0 8 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (a : BitVec 64) (b : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ (CStack s 0 8) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧ ((s'.regs 0).toNat = (a.toNat + b.toNat) % 2 ^ 64)) :=
  ⟨a0, b0, ret, s0, hret, call, pre, correctness a0 b0 ret hret s0 call pre⟩

end Witness

end Proof
