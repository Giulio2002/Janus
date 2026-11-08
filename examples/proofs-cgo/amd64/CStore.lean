import Extracted

/-!
# `void c_store(uint64_t *p, uint64_t v)` (C, amd64): `*p = v`

**Guarantee.** For every pointer `p` to 8 writable bytes (below `2^48`) that do not overlap the
return-address slot at `[RSP]`, and every value `v`, every System V call of the gcc-compiled
`c_store` (return address readable at `[RSP]`) returns without faulting, restores `RSP + 8`,
`RBX RBP R12–R15` and the direction flag, and the only change to memory is the word at `p`,
which becomes `v`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.CABI Janus.Amd64.Tactic

namespace Proof

theorem correctness (p v : BitVec 64) :
    CEnsures Extracted.program Extracted.entry [p, v]
      (fun s => CStack s 0 8 ∧ p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true ∧
        Disjoint p 8 (s.regs 4) 8)
      (fun s s' => s'.mem = s.mem.writeLE p.toNat 8 v.toNat) := by
  intro ret hret s hs ⟨⟨_, _, hnw, hacc⟩, hb, hp, hd⟩
  have h_rip := hs.rip
  have h_ret := hs.ret
  have h_df := hs.df
  have h_a0 : s.regs 7 = p := hs.reg (i := 0) (by simp)
  have h_a1 : s.regs 6 = v := hs.reg (i := 1) (by simp)
  simp only [CABI.regSP, Nat.sub_zero, Nat.zero_add, Program.withExit] at hacc hnw h_ret
  simp only [Disjoint] at hd
  janus64_run

namespace Witness

def ret : Nat := 0x1000
def wsp : Nat := 0x20008  -- addr-ok: a chosen stack window, not a binary address
def D : Nat := 0x100000  -- addr-ok: a chosen data window
def p0 : BitVec 64 := BitVec.ofNat 64 D
def v0 : BitVec 64 := 0x1234#64

/-- The stack window `[wsp - 64, wsp + 64)` (writable); the return address at `[wsp]`. -/
def smem : Janus.Arm64.Memory :=
  ⟨fun a => if wsp ≤ a ∧ a < wsp + 8 then BitVec.ofNat 8 (ret / 256 ^ (a - wsp)) else 0,
   [⟨wsp - 64, 128, true⟩, ⟨D, 8, true⟩]⟩

def s0 : State :=
  { regs := fun i => if i = 7 then p0 else if i = 6 then v0 else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := smem }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem call : CCall (Extracted.program.withExit ret) Extracted.entry [p0, v0] s0 :=
  ⟨rfl, by decide, by decide, by intro i h; simp only [List.length_cons, List.length_nil] at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, by decide, rfl⟩

theorem pre : CStack s0 0 8 ∧ p0.toNat + 8 ≤ 2 ^ 48 ∧ s0.mem.accessible p0.toNat 8 true = true ∧ Disjoint p0 8 (s0.regs 4) 8 := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, ?_⟩
  unfold Janus.Amd64.GoABI.Disjoint; decide

/-- The hypotheses of `correctness` hold together and the call returns with its guarantee. -/
theorem nonvacuous : ∃ (p : BitVec 64) (v : BitVec 64) (ret : Nat) (s : State), RetAddr Extracted.program ret ∧
    CCall (Extracted.program.withExit ret) Extracted.entry [p, v] s ∧ (CStack s 0 8 ∧ p.toNat + 8 ≤ 2 ^ 48 ∧ s.mem.accessible p.toNat 8 true = true ∧ Disjoint p 8 (s.regs 4) 8) ∧
    Returns (Extracted.program.withExit ret) s (fun s' => CReturn s s' ∧ (s'.mem = s.mem.writeLE p.toNat 8 v.toNat)) :=
  ⟨p0, v0, ret, s0, hret, call, pre, correctness p0 v0 ret hret s0 call pre⟩

end Witness

end Proof
