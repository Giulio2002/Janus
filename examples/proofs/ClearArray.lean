import Extracted

/-!
# `ClearArray(p *[5]uint64)`: `clear` on an array

**Guarantee.** For every pointer `p` to 40 writable bytes (`Ptr`) and every Go call state of
`example.com/basic.ClearArray`, the call returns (never faulting or panicking), obeys the ABI, all
40 bytes of `*p` are zero afterwards (the 320-bit little-endian value at `p` is `0`), and nothing
outside `[p, p + 40)` changes (`OnlyWrites`).

`clear(p[:])` of a 5-word array compiles to two `stp xzr, xzr` and one `str xzr`; no call to
`memclrNoHeapPointers`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (p : BitVec 64) :
    Ensures Extracted.program Extracted.entry [p] (fun s => Ptr s.mem p 40 true)
      (fun s s' => s'.mem.readLE p.toNat 40 = 0 ∧ OnlyWrites s.mem s'.mem p.toNat 40) := by
  intro ret hret s hs ⟨hp, hp'⟩
  janus_intro hs
  janus_run
  rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl, Memory.readLE_add, Memory.readLE_add,
    Memory.readLE_add, Memory.readLE_add]
  janus_simp

end Proof
