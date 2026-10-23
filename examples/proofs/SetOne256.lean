import Extracted

/-!
# `SetOne256(z *[4]uint64)` stores the 256-bit value 1 into `z` (a `.rodata` constant)

**Guarantee.** For every pointer `z` and every Go call state `s` of
`example.com/basic.SetOne256` (`z` in `X0`) in which the 32 bytes at `z` are writable and memory
holds the program's read-only data (`Program.DataLoaded`: the 32-byte `.rodata` constant
`{1, 0, 0, 0}` that the code loads with `adrp`/`add`/`ldp`, copied from the binary and checked by
`janus verify`), the call returns (never faulting or panicking), obeys the ABI, the value at `z` is `1`, and no other byte
changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof


theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => Ptr32 s.mem z true ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => val256 s'.mem z.toNat = 1 ∧ OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, hd⟩
  janus_intro hs
  janus_data hd
  janus_run



end Proof
