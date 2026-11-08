import Extracted

/-!
# `void c_store(uint64_t *p, uint64_t v)` (C, arm64): `*p = v`

**Guarantee.** For every pointer `p` to 8 writable bytes (below `2^48`) and every value `v`,
every AAPCS64 call of the gcc-compiled `c_store` returns without faulting, restores `SP` and
`X19`–`X29`, and the only change to memory is the word at `p`, which becomes `v`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.CABI Janus.Tactic

namespace Proof

theorem correctness (p v : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, v]
      (fun s => p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true)
      (fun s s' => s'.mem = s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨hb, hacc⟩
  janus_intro hs.call
  janus_run

namespace Witness

def RET : Nat := 0x1000
def P : Nat := 0x100000
def v0 : BitVec 64 := 0x1234#64

def s0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 P else if i = 1 then v0 else if i = 30 then BitVec.ofNat 64 RET else 0,
    sp := BitVec.ofNat 64 0x300000, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := ⟨fun _ => 0, [⟨P, 8, true⟩]⟩, exclPass := fun _ => true }

theorem hret : RetAddr Extracted.program RET := RetAddr.of_check (by decide +kernel)

theorem call : CCall (Extracted.program.withExit RET) Extracted.entry [BitVec.ofNat 64 P, v0] s0 :=
  ⟨⟨rfl, rfl, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩, by decide, by decide⟩

theorem pre : (BitVec.ofNat 64 P).toNat + 8 ≤ 2 ^ 48 ∧ s0.mem.accessible (BitVec.ofNat 64 P).toNat 8 true = true :=
  ⟨by decide, by decide⟩

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (p v : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [p, v] s ∧
    (p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧
      s'.mem = s.mem.writeLE p.toNat 8 v.toNat) :=
  ⟨_, v0, RET, s0, hret, call, pre, correctness _ v0 RET hret s0 call pre⟩

end Witness

end Proof
