import Extracted

/-!
# `uint64_t c_add(uint64_t a, uint64_t b)` (C, arm64): returns `a + b`

**Guarantee.** For all 64-bit `a` and `b`, every AAPCS64 call of the gcc-compiled `c_add` (any
admissible return address in `X30`, `SP` 16-byte aligned; every other register, the flags and
memory arbitrary) returns after finitely many steps without faulting, restores `SP` and the
callee-saved registers `X19`–`X29` (`CReturn`), and leaves `(a + b) mod 2^64` in `X0`.

The code is `add x0, x0, x1; ret`, copied from the cgo example binary.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic

namespace Proof

theorem correctness (a b : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [a, b] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs _
  janus_intro hs.call
  janus_run

namespace Witness

def RET : Nat := 0x1000
def a0 : BitVec 64 := 3#64
def b0 : BitVec 64 := 4#64

def s0 : State :=
  { regs := fun i => if i = 0 then a0 else if i = 1 then b0 else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 0x300000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := ⟨fun _ => 0, []⟩, exclPass := fun _ => true }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [a0, b0] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩, by decide, by decide⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (a b : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ True ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      (s'.regs 0).toNat = (a.toNat + b.toNat) % 2 ^ 64) :=
  ⟨a0, b0, RET, s0, hret, call, trivial, correctness a0 b0 RET hret s0 call trivial⟩

end Witness

end Proof
