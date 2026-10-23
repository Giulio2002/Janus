import Janus
import Extracted

/-! `example.com/basic.Mul64` on amd64 (`MULQ BX; MOVQ AX, BX; MOVQ DX, AX; RET`): the full 128-bit product `(hi, lo)`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ hi lo, r = [hi, lo] ∧ hi.toNat * 2 ^ 64 + lo.toNat = x.toNat * y.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  have hp : x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' x.isLt y.isLt
  generalize x.toNat * y.toNat = p at hp ⊢
  simp only [BitVec.toNat_ofNat]
  omega

end Proof
