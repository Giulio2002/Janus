import Janus
import Extracted

/-! `example.com/basic.Add256(z, x, y *[4]uint64)` on amd64: `*z = *x + *y mod 2^256`.

Four loads of each operand, an `ADDQ` and three `ADCQ`, four stores. The precondition gives the
three 32-byte buffers (`z` writable, `x`, `y` readable), the return-address slot, and that `z`
overlaps neither the operands nor the return-address slot (the operands may alias each other). -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem readLE_32 (m : Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem carry_toNat (t : Nat) (h : t < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ t)).toNat = t / 18446744073709551616 := by
  by_cases h' : 18446744073709551616 ≤ t
  · simp [h']; omega
  · simp [h']; omega

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Buffer s y 32 false ∧ Disjoint z 32 x 32 ∧ Disjoint z 32 y 32 ∧
        Disjoint z 32 (s.regs regSP) 8)
      (fun s s' => valueAt s' z 32 = (valueAt s x 32 + valueAt s y 32) % 2 ^ 256) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdx, hdy, hds⟩ := hpre
  simp only [Disjoint, regSP, Nat.sub_zero, Nat.zero_add] at hacc hdx hdy hds
  simp only [valueAt]
  janus64_run [readLE_32]
  have b := fun a => Janus.Arm64.Memory.readLE_lt s.mem a 8
  have := b x.toNat; have := b (x.toNat + 8); have := b (x.toNat + 16); have := b (x.toNat + 24)
  have := b y.toNat; have := b (y.toNat + 8); have := b (y.toNat + 16); have := b (y.toNat + 24)
  simp only [Nat.reducePow] at *
  simp (disch := omega) only [carry_toNat]
  omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def z : BitVec 64 := 0x30800#64
def x : BitVec 64 := 0x30900#64
def y : BitVec 64 := 0x30a00#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then y else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Buffer s y 32 false ∧ Disjoint z 32 x 32 ∧ Disjoint z 32 y 32 ∧
        Disjoint z 32 (s.regs regSP) 8) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64) (x : BitVec 64) (y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Buffer s y 32 false ∧ Disjoint z 32 x 32 ∧ Disjoint z 32 y 32 ∧
        Disjoint z 32 (s.regs regSP) 8) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ valueAt s' z 32 = (valueAt s x 32 + valueAt s y 32) % 2 ^ 256) :=
  ⟨ret, s0, z, x, y, hret, setup, hpre, correctness z x y ret hret s0 setup hpre⟩

end Witness

end Proof
