import Janus
import Extracted

/-! `example.com/basic.Add` on amd64: `ADDQ BX, AX; RET` returns `x + y`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 0 8) (fun r => r = [x + y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

end Proof
