import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E1d: `decide` with the trusted scoped instance `Classical.propDecidable` written
inline. It passes `checkInstArgs` (a registered trusted instance), but the printed
`decide (x = 0)` re-elaborates with `instDecidableEqBitVec`. Both mean the same proposition
(`Decidable p` is a subsingleton) yet they are not definitionally equal, so the round trip
rejects it: expected Invalid (over-strict, never misleading). -/
namespace Proof
theorem correctness (x y : BitVec 64) (_h : @decide (x = 0) (Classical.propDecidable _) = false) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x + y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
