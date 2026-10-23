import Extracted

/-! Must be rejected by the axiom audit of `janus verify` (depends on `sorryAx`). -/

namespace Proof

theorem correctness : Extracted.program.segments.length = 7 := sorry

end Proof
