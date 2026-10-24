import Extracted

/-!
# `Table(i uint64) uint64`: entry `i & 7` of a constant `[8]uint64` (a `.rodata` literal)

**Guarantee.** For every 64-bit `i` and every Go call state `s` of `example.com/basic.Table` whose
memory holds the function's read-only data (`DataLoaded`), that satisfies Go's frame-pointer
invariant (`FPConvention`) and whose `SP` is aligned with `[SP-88, SP)` writable, the call
returns (never faulting or panicking), obeys the ABI, and `X0 = table[i mod 8]` for the table of
the Go source. The code copies the 64-byte literal from `.rodata` into its frame (four
`ADRP`/`ADD`/`LDP` and four `STP`) and loads `t[i&7]` from the frame.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

/-- The Go source's table. -/
def table : List (BitVec 64) :=
  [0x243f6a8885a308d3, 0x13198a2e03707344, 0xa4093822299f31d0, 0x082efa98ec4e6c89,
   0x452821e638d01377, 0xbe5466cf34e90c6c, 0xc0ac29b7c97c50dd, 0x3f84d5b5b5470917]

theorem correctness (i : BitVec 64) :
    Ensures Extracted.program Extracted.entry [i]
      (fun s => Extracted.program.DataLoaded s.mem ∧ FPConvention s ∧ StackOK s 88 0)
      (fun _ s' => s'.regs 0 = table[i.toNat % 8]!) := by
  intro ret hret s hs ⟨hd, hfp, ⟨hal, hb, ha, hw⟩⟩
  janus_intro hs
  simp only [FPConvention, regFP] at hfp
  janus_data hd [hw]
  janus_run
  generalize hk : i.toNat % 8 = k
  have hlt : k < 8 := hk ▸ Nat.mod_lt _ (by decide)
  janus_cases hlt
  all_goals janus_simp [table]

end Proof
