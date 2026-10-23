import Extracted

/-!
# `A64Equal64(a, b *[64]byte)`: `bytes.Equal(a[:], b[:])` through `runtime.memequal`'s SIMD loop

**Guarantee.** For all pointers `a`, `b` and every Go call state `s` of
`example.com/basic.A64Equal64` such that
* the stack-growth prologue falls through (`GuardOK s 0`), `SP` is aligned and the 24 bytes
  below `SP` are writable (the 16-byte frame and the saved frame pointer),
* the 64 bytes at `a` and the 64 bytes at `b` are readable, and neither array overlaps that
  stack window (the arrays may overlap each other, or be the same array),

the call returns (never faulting or panicking), obeys the ABI, and returns `1` (`true`) in `X0`
if the 64 bytes at `a` equal the 64 bytes at `b`, and `0` (`false`) otherwise.

**What this covers.** `bytes.Equal` is inlined: with the length known to be 64 it becomes a call
`runtime.memequal(a, b, 64)`. The proof executes both functions instruction by instruction from
the extracted words, including memequal's 64-byte SIMD loop: two `LD1 {v0.2d-v3.2d}` loads,
four `CMEQ .2D` (each 64-bit lane all-ones iff equal), three `AND .16B`, two `UMOV x, v.d[i]`
and the `CBZ` tests, plus the shortcut for `a = b`. The vector registers are part of the state
(`State.vregs`), arbitrary at the call, and the model of each instruction is checked against
qemu and the Arm ASL (Sail) model (`docs/ORACLE.md`, `docs/ORACLE-SAIL.md`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

set_option maxHeartbeats 4000000 in
theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ StackOK s 24 0 ∧ Ptr s.mem a 64 false ∧ Ptr s.mem b 64 false ∧
        Disjoint a.toNat 64 (s.sp.toNat - 24) 24 ∧ Disjoint b.toNat 64 (s.sp.toNat - 24) 24)
      (fun s s' => s'.regs 0 = if s.mem.readLE a.toNat 64 = s.mem.readLE b.toNat 64 then 1 else 0) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hA, hA'⟩, ⟨hB, hB'⟩, hda, hdb⟩
  janus_intro hs
  simp only [Disjoint] at hda hdb
  -- Executes A64Equal64 and memequal; the branches of the SIMD loop's two `CBZ`s come out as
  -- "words 0, 2, 4, 6 are equal" and "words 1, 3, 5, 7 are equal" (`elem_cmeq`, `ite_land_ite`).
  janus_run
  -- 64 bytes are equal iff their eight words are.
  all_goals simp only [readLE_64_eq_iff, Nat.add_assoc, Nat.reduceAdd] at *
  all_goals split <;> simp_all

end Proof
