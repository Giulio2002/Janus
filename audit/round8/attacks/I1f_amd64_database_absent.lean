import Janus
import Extracted
/-! ATTACK I1f (expected BLOCKED, amd64): `dataBase Extracted.program 3` names data object 3 of
the amd64 extraction of Add, which has none, so it is `0`. The statement reads "Add returns
x + y + the address of data object 3"; it holds only because the address silently defaults. -/
namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 0 8)
      (fun r => r = [x + y + BitVec.ofNat 64 (dataBase Extracted.program 3)]) := by
  have h0 : dataBase Extracted.program 3 = 0 := by rfl
  rw [h0]; simp only [BitVec.add_zero]
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

end Proof
