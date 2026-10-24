import Extracted
import MisLib

/-! Round 7 consumer proof against the MisLib dependency (example.com/basic.Add). -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace R7Proofs

/-- J1a: "Add returns `MisLib.mul x y`". `MisLib.mul` is documented as the product, but its
body is `a + b`, so this is the honest "Add returns x + y". Before round 7 the report listed
`MisLib.mul (def, MisLib)` by name only; round 7 discloses its body. Expected Verified, with
`MisLib.mul … := fun a b => a + b` in the report. -/
theorem misnamed (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = MisLib.mul x y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
  simp only [MisLib.mul]

end R7Proofs
