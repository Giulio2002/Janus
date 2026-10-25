import Janus
import Extracted

/-! `example.com/basic.Mod(x, y uint64) uint64` on amd64: `%` by a variable.

`correctness`: for `y ≠ 0` the call returns `x mod y` (the remainder `RDX` of `DIVQ`);
`panics`: for `y = 0` it reaches the Go panic stub `runtime.panicdivide`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) (hy : y ≠ 0) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 16 8)
      (fun r => ∃ v, r = [v] ∧ v.toNat = x.toNat % y.toNat) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq h)
  janus64_run
  refine ⟨_, rfl, ?_⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt)]

theorem panics (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, 0] s)
    (hpre : StackWritable s 16 8) : Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  janus64_run

end Proof
