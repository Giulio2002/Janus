import Janus
import Extracted

/-! `example.com/basic.ReverseArray(out, in *[4]uint64)` on amd64: array value semantics and
range over an array.

For all pointers `out` (32 writable bytes) and `in` (32 readable bytes) that are the same array
or disjoint, both disjoint from the stack window `[RSP-72, RSP+8)`, afterwards
`out[i] = in[3 - i]` for every `i < 4`, with `in` read **before** the call; so also for
`out = in`. `a := *in` copies the array into the frame (two 16-byte `MOVUPS` through `X14`,
then a second copy for the `range` operand), and the loop reads the copy. The loop has a constant
trip count, so the run executes it. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- An 8-byte half of a 16-byte read, as left by the `MOVUPS` copies. -/
theorem half (m : Memory) (a k j : Nat) (hk : k = j) (hj : j = 0 ∨ j = 8) :
    m.readLE a 16 / 256 ^ k % 18446744073709551616 = m.readLE (a + j) 8 := by
  subst hk
  rw [Janus.Arm64.Memory.readLE_div m a 16 k (by omega),
    show (18446744073709551616 : Nat) = 256 ^ 8 from rfl,
    Janus.Arm64.Memory.readLE_mod m _ _ 8 (by omega)]

/-- The same half with the (redundant) `% 2^64` already dropped by the executor's simp set, as it
leaves the high half of a 16-byte read: `v / 2^64` of a 16-byte value is below `2^64`. -/
theorem half_hi (m : Memory) (a : Nat) :
    m.readLE a 16 / 18446744073709551616 = m.readLE (a + 8) 8 := by
  rw [show (18446744073709551616 : Nat) = 256 ^ 8 from rfl, Janus.Arm64.Memory.readLE_div m a 16 8 (by omega)]

/-- The low half, as `v / 1 % 2^64`. -/
theorem half_lo (m : Memory) (a : Nat) :
    m.readLE a 16 / 1 % 18446744073709551616 = m.readLE a 8 := half m a 0 0 rfl (by omega)

set_option maxHeartbeats 2000000 in
theorem correctness (out inp : BitVec 64) :
    Ensures Extracted.program Extracted.entry [out, inp]
      (fun s => StackWritable s 72 8 ∧ Buffer s out 32 true ∧ Buffer s inp 32 false ∧
        (out = inp ∨ Disjoint out 32 inp 32) ∧
        ((s.regs regSP).toNat + 8 ≤ out.toNat ∨ out.toNat + 32 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ inp.toNat ∨ inp.toNat + 32 ≤ (s.regs regSP).toNat - 72))
      (fun s s' => ∀ i < 4, s'.mem.readLE (out.toNat + 8 * i) 8 =
        s.mem.readLE (inp.toNat + 8 * (3 - i)) 8) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨hle, hnw, hacc⟩, ⟨hob, ho⟩, ⟨hib, hi⟩, hoi, hdo, hdi⟩ := hpre
  simp only [regSP] at hacc hle hnw hdo hdi
  rcases hoi with rfl | hoi
  all_goals try simp only [Disjoint] at hoi
  all_goals janus64_run
  all_goals intro i hi4; janus64_cases hi4
  all_goals janus64_simp
  all_goals first
    | exact half_hi _ _
    | exact half_lo _ _
    | with_reducible exact half _ _ _ 0 (by omega) (by omega)
    | (rw [half _ _ _ 8 (by omega) (by omega)]; done)
    | (rw [half _ _ _ 0 (by omega) (by omega), Nat.add_zero]; done)
    | exact half _ _ _ 0 (by omega) (by omega)
    | (rw [half _ _ _ 8 (by omega) (by omega)])
    | (rw [half _ _ _ 0 (by omega) (by omega), Nat.add_zero])

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)
def out : BitVec 64 := 0x30800#64 -- addr-ok: synthetic witness constant (stack/heap window of the concrete call state)
def inp : BitVec 64 := 0x30a00#64

def s0 : State :=
  { regs := fun i => if i = 0 then out else if i = 3 then inp else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [out, inp] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩
theorem hpre : (fun s => StackWritable s 72 8 ∧ Buffer s out 32 true ∧ Buffer s inp 32 false ∧
        (out = inp ∨ Disjoint out 32 inp 32) ∧
        ((s.regs regSP).toNat + 8 ≤ out.toNat ∨ out.toNat + 32 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ inp.toNat ∨ inp.toNat + 32 ≤ (s.regs regSP).toNat - 72)) s0 := by
  try dsimp only [Janus.Amd64.GoABI.Disjoint, Janus.Spec.Disjoint]
  repeat' apply And.intro
  all_goals first | decide | (refine ⟨?_, ?_, ?_⟩ <;> decide)

/-- All hypotheses of `correctness` hold together. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (out : BitVec 64) (inp : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [out, inp] s ∧ (StackWritable s 72 8 ∧ Buffer s out 32 true ∧ Buffer s inp 32 false ∧
        (out = inp ∨ Disjoint out 32 inp 32) ∧
        ((s.regs regSP).toNat + 8 ≤ out.toNat ∨ out.toNat + 32 ≤ (s.regs regSP).toNat - 72) ∧
        ((s.regs regSP).toNat + 8 ≤ inp.toNat ∨ inp.toNat + 32 ≤ (s.regs regSP).toNat - 72)) ∧
    (Returns (Extracted.program.withExit ret) s fun s' =>
    ABIReturn s s' ∧ ∀ i < 4, s'.mem.readLE (out.toNat + 8 * i) 8 =
        s.mem.readLE (inp.toNat + 8 * (3 - i)) 8) :=
  ⟨ret, s0, out, inp, hret, setup, hpre, correctness out inp ret hret s0 setup hpre⟩

end Witness

end Proof
