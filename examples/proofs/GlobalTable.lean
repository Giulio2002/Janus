import Extracted

/-!
# `GlobalTable(i uint64) uint64`: indexing a writable package array

**Guarantee.** For every 64-bit `i` and every Go call state `s` of
`example.com/basic.GlobalTable` whose memory makes the 64 bytes of the package variable
`example.com/basic.tbl` (a `[8]uint64` in `.noptrdata`) readable, the call returns (never faulting
or panicking), obeys the ABI, and `X0 = tbl[i & 7]`, the word at `tbl + 8·(i mod 8)` in the
memory at the call. The variable is writable, so its contents are not taken from the binary:
the theorem holds for whatever the program stored there. `tbl` is the address the code computes
(`ADRP` + `ADD`), recomputed from the extracted words.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- Address of `example.com/basic.tbl`: `ADRP` (word 1) plus the `ADD` immediate (word 2, the
same 12-bit field as an unscaled `LDR` offset). -/
def tbl : Nat :=
  adrpLdTarget (Extracted.entry + 4) (segWord Extracted.program "example.com/basic.GlobalTable" 1)
    (segWord Extracted.program "example.com/basic.GlobalTable" 2) 0

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i] (fun s => s.mem.accessible tbl 64 false = true)
      (fun s s' => (s'.regs 0).toNat = s.mem.readLE (tbl + 8 * (i.toNat % 8)) 8) := by
  intro ret hret s hs ht
  janus_intro hs
  janus_eval_nat h_t : tbl
  rw [h_t] at ht ⊢
  janus_run

end Proof
