import Extracted

/-! A placeholder theorem for exercising `janus verify` end to end before the ISA model can
run real code. It says nothing about the behaviour of the extracted function. -/

namespace Proof

theorem correctness : Extracted.entry = Extracted.entry := rfl

end Proof
