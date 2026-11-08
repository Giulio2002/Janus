import Janus
import Extracted

/-! `example.com/basic.SwapBig(a, b *Big)` on amd64: struct assignment by value (a 64-byte
struct).

For all pointers `a`, `b` to 64 writable bytes that are the same struct or disjoint, both
disjoint from the stack window `[RSP-72, RSP+8)`, afterwards every word `i < 8` of `*a` is word
`i` of `*b` before the call and vice versa (for `a = b`: unchanged). `*a, *b = *b, *a` copies
`*a` into a frame temporary, `*b` over `*a`, then the temporary over `*b`, each as four 16-byte
`MOVUPS` through `X14`; no `memmove` or `duffcopy`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- An 8-byte half of a 16-byte read, as left by the `MOVUPS` copies. -/
theorem half (m : Memory) (a k j : Nat) (hk : k = j) (hj : j = 0 ∨ j = 8) :
    m.readLE a 16 / 256 ^ k % 18446744073709551616 = m.readLE (a + j) 8 := by
  subst hk
  rw [Janus.Arm64.Memory.readLE_div m a 16 k (by omega),
    show (18446744073709551616 : Nat) = 256 ^ 8 from rfl,
    Janus.Arm64.Memory.readLE_mod m _ _ 8 (by omega)]

theorem half0 (m : Memory) (a : Nat) :
    m.readLE a 16 / 256 ^ 0 % 18446744073709551616 = m.readLE a 8 := half m a 0 0 rfl (by omega)

theorem half8 (m : Memory) (a : Nat) :
    m.readLE a 16 / 256 ^ 8 % 18446744073709551616 = m.readLE (a + 8) 8 := half m a 8 8 rfl (by omega)

/-- The same, with the power evaluated and the (redundant) modulus dropped, as the simp set leaves it. -/
theorem half8' (m : Memory) (a : Nat) :
    m.readLE a 16 / 18446744073709551616 = m.readLE (a + 8) 8 := by
  have := half8 m a
  rw [show (256 : Nat) ^ 8 = 18446744073709551616 from rfl] at this
  rw [← this]
  exact (Nat.mod_eq_of_lt (by
    have := Janus.Arm64.Memory.readLE_lt m a 16
    omega)).symm

/-- The low half with the shift already evaluated (`256 ^ 0` is `1` once the executor has computed the
same-base address difference). -/
theorem half0' (m : Memory) (a : Nat) :
    m.readLE a 16 / 1 % 18446744073709551616 = m.readLE a 8 := half m a 0 0 rfl (by omega)

set_option maxHeartbeats 4000000 in
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => StackWritable s 72 8 ∧ Buffer s a 64 true ∧ Buffer s b 64 true ∧
        (a = b ∨ Disjoint a 64 b 64) ∧
        ((s.regs regSP).toNat + 8 ≤ a.toNat ∨ a.toNat + 64 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ b.toNat ∨ b.toNat + 64 ≤ (s.regs regSP).toNat - 72))
      (fun s s' => ∀ i < 8, s'.mem.readLE (a.toNat + 8 * i) 8 = s.mem.readLE (b.toNat + 8 * i) 8 ∧
        s'.mem.readLE (b.toNat + 8 * i) 8 = s.mem.readLE (a.toNat + 8 * i) 8) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, ⟨hab', ha⟩, ⟨hbb, hb⟩, hab, hda, hdb⟩ := hpre
  simp only [regSP] at hacc hle hnw hda hdb
  rcases hab with rfl | hab
  all_goals try simp only [Disjoint] at hab
  all_goals janus64_run
  all_goals intro i hi8; janus64_cases hi8
  all_goals janus64_simp
  all_goals try simp only [Nat.sub_self, Nat.add_sub_cancel_left, half0, half0', half8, half8', and_self,
    Nat.add_assoc, Nat.reduceAdd]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def a : BitVec 64 := 0x30800#64
def b : BitVec 64 := 0x30a00#64

def s0 : State :=
  { regs := fun i => if i = 0 then a else if i = 3 then b else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 72 8 ∧ Buffer s a 64 true ∧ Buffer s b 64 true ∧
        (a = b ∨ Disjoint a 64 b 64) ∧
        ((s.regs regSP).toNat + 8 ≤ a.toNat ∨ a.toNat + 64 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ b.toNat ∨ b.toNat + 64 ≤ (s.regs regSP).toNat - 72)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (a : BitVec 64) (b : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [a, b] s ∧ (StackWritable s 72 8 ∧ Buffer s a 64 true ∧ Buffer s b 64 true ∧
        (a = b ∨ Disjoint a 64 b 64) ∧
        ((s.regs regSP).toNat + 8 ≤ a.toNat ∨ a.toNat + 64 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ b.toNat ∨ b.toNat + 64 ≤ (s.regs regSP).toNat - 72)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∀ i < 8, s'.mem.readLE (a.toNat + 8 * i) 8 = s.mem.readLE (b.toNat + 8 * i) 8 ∧
        s'.mem.readLE (b.toNat + 8 * i) 8 = s.mem.readLE (a.toNat + 8 * i) 8) :=
  ⟨ret, s0, a, b, hret, setup, hpre, correctness a b ret hret s0 setup hpre⟩

end Witness

end Proof
