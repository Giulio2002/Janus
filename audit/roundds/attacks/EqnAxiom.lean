import Extracted
/-! ATTACK (equation-lemma exemption): an AXIOM named like a generated equation lemma -/
axiom Extracted.dataSize.«example.com/basic.symPows».eq_1 : Extracted.dataSize.«example.com/basic.symPows» = 65
namespace Proof
theorem correctness : Extracted.entry = Extracted.entry := rfl
end Proof
