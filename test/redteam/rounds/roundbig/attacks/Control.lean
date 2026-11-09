import Extracted
/-! CONTROL: a statement about the extracted code of a tree-shaped extraction verifies; it reads the chunks only
through `Extracted.program`. -/
namespace Proof
theorem correctness : Extracted.program.segments.length = 1 := by decide
end Proof
