import Extracted
/-! ATTACK: a proof module declares its own chunk of the generated code in the reserved `Extracted` namespace
(`Extracted.seg0_bytes_9999` / `seg0_words_9999` is a name the generator never emits). Only the generated module
may declare names under `Extracted`. -/
def Extracted.seg0_chunk_9999 : List Nat := []
namespace Proof
theorem correctness : Extracted.program.segments.length = 1 := by decide
end Proof
