import Janus
import Extracted

/-! `example.com/basic.Div` on amd64: `x / y` for `y ≠ 0` (`DIVQ`), and a Go panic (`runtime.panicdivide`) for `y = 0`. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

theorem correctness (x y : BitVec 64) (hy : y ≠ 0) :
    EnsuresResults Extracted.program Extracted.entry [x, y] 1
      (fun s => StackWritable s 16 8)
      (fun r => r = [x / y]) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  have hy' : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq h)
  janus64_run
  first | (with_reducible congr 1; with_reducible congr 1) | (congr 1; congr 1)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_udiv, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt)]

theorem panics (x : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [x, 0] s)
    (hpre : StackWritable s 16 8) : Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  janus64_run

end Proof
