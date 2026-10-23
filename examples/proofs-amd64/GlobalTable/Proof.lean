import Janus
import Extracted

/-! `example.com/basic.GlobalTable(i)` on amd64: `tbl[i&7]`, where `tbl` (`example.com/basic.tbl`,
64 bytes at `tbl` in the writable `.noptrdata`) is memory the caller provides. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Address of `example.com/basic.tbl` in this binary (`identity.json`, `skippedData`). -/
def tbl : Nat := 0x54d7e0

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible tbl 64 false = true)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (s.mem.readLE (tbl + i.toNat % 8 * 8) 8)]) := by
  intro ret hret s hs hpre
  simp only [tbl] at *
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ht⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

end Proof
