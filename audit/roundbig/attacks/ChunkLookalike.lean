import Extracted
/-! ATTACK: a lookalike-letter namespace (Greek capital epsilon `Ε` in `Εxtracted`) for a chunk definition. The reserved-name rule
folds lookalike letters. -/
def Εxtracted.seg0_CHUNK_9999 : List Nat := []
namespace Proof
theorem correctness : Extracted.program.segments.length = 1 := by decide
end Proof
