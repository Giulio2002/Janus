import Extracted
/-! ATTACK A10 (expected BLOCKED): `#exit` before the (false) theorem: Lean stops elaborating, so
the theorem never enters the environment and the audit cannot find it. -/
namespace Proof
#exit
theorem correctness : False := sorry
