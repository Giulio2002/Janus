import Janus
import Extracted

/-! `example.com/basic.GlobalTable(i)` on amd64: `tbl[i&7]`, where `tbl` (`example.com/basic.tbl`,
64 bytes at `tbl` in the writable `.noptrdata`) is memory the caller provides. -/

namespace Proof
open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- Address of `example.com/basic.tbl`: the RIP-relative operand of the `LEAQ tbl(SB), CX` at
offset 3, read off the extracted code (layout-independent). -/
def tbl : Nat := ripTarget Extracted.program (Extracted.entry + 3)

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => StackWritable s 0 8 ∧ s.mem.accessible tbl 64 false = true)
      (fun s s' => results 1 s' = [BitVec.ofNat 64 (s.mem.readLE (tbl + i.toNat % 8 * 8) 8)]) := by
  intro ret hret s hs hpre
  simp only [tbl] at *
  janus64_addrs
  janus64_intro hs
  obtain ⟨⟨-, hnw, hacc⟩, ht⟩ := hpre
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  janus64_run

end Proof
