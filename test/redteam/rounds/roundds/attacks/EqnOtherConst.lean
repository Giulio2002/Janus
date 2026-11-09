import Extracted
/-! ATTACK (equation-lemma exemption): an eq_1 theorem under a name that is not a constant of the Extracted module -/
theorem Extracted.dataSize.«example.com/basic.nothere».eq_1 : Extracted.dataSize.«example.com/basic.symPows» = 64 := rfl
namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
end Proof
