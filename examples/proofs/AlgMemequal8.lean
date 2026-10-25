import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Mem

namespace Proof

theorem correctness (d : Nat) : MemequalN Extracted.program Extracted.entry d 1 := by
  intro s hpc ⟨⟨hg, ⟨hl1, hl2, hc⟩⟩, ⟨ha1, ha2, ha3⟩, ⟨hb1, hb2, hb3⟩⟩
  janus_run
  refine EqRet.intro rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) rfl rfl rfl
    (MemFrame.refl _ _) ?_
  simp [BoolRes, setReg]
  simp only [Nat.shiftLeft_eq, Nat.mul_mod_left, Nat.or_zero,
    show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h0 := (s.mem.bytes (s.regs 0).toNat).isLt
  have h1 := (s.mem.bytes (s.regs 1).toNat).isLt
  generalize (s.mem.bytes (s.regs 0).toNat).toNat = x at *
  generalize (s.mem.bytes (s.regs 1).toNat).toNat = y at *
  have hx : (if x < 128 then x else x + 18446744073709551360) % 18446744073709551616 % 4294967296 % 2 ^ 8 % 2 ^ 8 = x := by
    split <;> omega
  have hy : (if y < 128 then y else y + 18446744073709551360) % 18446744073709551616 % 4294967296 % 2 ^ 8 % 2 ^ 8 = y := by
    split <;> omega
  rw [hx, hy]
  by_cases h : y = x
  · subst h; simp
  · have h' : (x == y) = false := beq_false_of_ne (Ne.symm h)
    simp [h, h']

end Proof
