module
public import Extracted
/-! M1: a `module` (Lean module system) proof file. Checks whether the auditor's
`importModules` sees the theorem body (for collectAxioms) when the proof module is compiled
under the module system, where theorem bodies live in the private olean part. -/
open Janus Janus.GoABI
namespace Proof
public theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => (s'.regs 0).toNat = (x.toNat + y.toNat + 1) % 2 ^ 64) := by
  sorry
end Proof
