import Extracted
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

/-! Round 5 E4c: a `local notation` for `^` (also global, meaning `HPow.hPow`) that means `+`.
The statement source reads `x ^ y`; the report prints what the term is (`x + y`), in a clean
environment without the proof's notation. Expected Verified with `x + y` printed. (A local
`*` is ambiguous with the global one and Lean refuses it; `macro_rules` is E4b.) -/
namespace Proof
local notation:75 a " ^ " b => HAdd.hAdd a b
theorem correctness (x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x, y] (fun _ => True)
      (fun _ s' => s'.regs 0 = x ^ y) := by
  intro ret hret s hs _
  janus_intro hs
  janus_run
end Proof
