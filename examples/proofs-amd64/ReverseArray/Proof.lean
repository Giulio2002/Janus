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
    | with_reducible exact half _ _ _ 0 (by omega) (by omega)
    | (rw [half _ _ _ 8 (by omega) (by omega)]; done)
    | (rw [half _ _ _ 0 (by omega) (by omega), Nat.add_zero]; done)
    | exact half _ _ _ 0 (by omega) (by omega)
    | (rw [half _ _ _ 8 (by omega) (by omega)])
    | (rw [half _ _ _ 0 (by omega) (by omega), Nat.add_zero])

end Proof
