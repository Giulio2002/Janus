import Extracted

/-!
# `TotalMeters(a, b Meters) uint64`: a generic function, through its dictionary

**Guarantee.** For all 64-bit `a`, `b` and every Go call state `s` of
`example.com/basic.TotalMeters` whose memory holds the function's read-only data
(`DataLoaded`: the dictionary of `total[Meters]`), whose stack-growth prologues fall through
(`GuardOK s 48`, the guard word outside the stack window) and whose `SP` is aligned with
`[SP-96, SP)` writable, the call returns (never faulting or panicking), obeys the ABI, and
`X0 = 100·(a + b) mod 2^64`: the length `a + b` metres in centimetres.

**What is exercised.** `total[T Scaler]` is compiled once per GC shape. `Meters` and `Feet`
(`TotalFeet.lean`) are both `uint64`, so both instantiations share the single body
`total[go.shape.uint64]`, and each caller passes its own dictionary in `X0`
(`..dict.total[Meters]`, in `.rodata`). The shape code finds the method `Scale` there: it loads
the dictionary's first word (the code address of `Meters.Scale`) and calls it with `blr`, twice.
The executor reads that word from the extracted dictionary, so the target is a literal and no
hypothesis about it is needed. (`Meters.Scale` is extracted with `--targets`,
`scripts/example-targets.sh`.)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Proof

theorem correctness (a b : BitVec 64) :
    Ensures Extracted.program Extracted.entry [a, b]
      (fun s => Extracted.program.DataLoaded s.mem ∧ GuardOK s 48 ∧ StackOK s 96 0 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 96) 96)
      (fun _ s' => (s'.regs 0).toNat = 100 * (a.toNat + b.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨hd, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hgd⟩
  janus_intro hs
  simp only [Disjoint] at hgd
  janus_data hd [hw]
  janus_run
  janus_arith

end Proof
