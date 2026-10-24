import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

/-! Round 9 I1g: `Program.contractAddr` falls back to address 0 for a name that is not a
recorded contract. `"runtime.newobjеct"` has a Cyrillic `е` (U+0435), so the hypothesis below
reads as the real `newobject` contract while it is about address 0 of a program whose
extraction has no contracts at all. Before round 9 the I1 name check did not cover
`contractAddr`, and this verified. -/
namespace Proof
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x y : BitVec 64)
    (_hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobjеct") rt 4096 H) :
    Ensures Extracted.program Extracted.entry [x, y] (fun s => GuardOK s 0 ∧ StackOK s 0 0)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat) % 2 ^ 64) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, hal, hb, ha, hw⟩
  janus_intro hs
  janus_run
  janus_arith
end Proof
