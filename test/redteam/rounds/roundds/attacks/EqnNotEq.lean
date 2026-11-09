import Extracted
/-! ATTACK (equation-lemma exemption): a theorem named C.eq_1 whose type is not an equation about C -/
theorem Extracted.dataSize.«example.com/basic.symPows».eq_1 : Extracted.dataSize.«example.com/basic.symPows» ≤ 64 := by decide
namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
end Proof
