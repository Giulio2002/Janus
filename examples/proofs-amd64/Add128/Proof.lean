import Janus
import Extracted

/-! `example.com/basic.Add128` on amd64 (`ADDQ DI, BX; ADCQ CX, AX; RET`): the 128-bit sum of
`xh:xl` and `yh:yl`, modulo `2^128`, returned as `(hi, lo)` in `RAX`, `RBX`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (xh xl yh yl : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [xh, xl, yh, yl] 2
      (fun s => StackWritable s 0 8)
      (fun r => ∃ hi lo, r = [hi, lo] ∧
        hi.toNat * 2 ^ 64 + lo.toNat =
          (xh.toNat * 2 ^ 64 + xl.toNat + (yh.toNat * 2 ^ 64 + yl.toNat)) % 2 ^ 128) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run
  refine ⟨_, _, rfl, ?_⟩
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  have := xl.isLt; have := yl.isLt; have := xh.isLt; have := yh.isLt
  omega

end Proof
