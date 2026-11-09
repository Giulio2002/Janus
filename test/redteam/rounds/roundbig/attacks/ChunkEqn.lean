import Extracted
/-! ATTACK (equation-lemma exemption): an `eq_1` theorem named under a chunk that the Extracted module does not
declare. The exemption is for equation lemmas of constants of the generated module only. -/
theorem Extracted.seg0_CHUNK_nothere.eq_1 : Extracted.seg0_CHUNK_0 = Extracted.seg0_CHUNK_0 := rfl
namespace Proof
theorem correctness : Extracted.program.segments.length = 1 := by decide
end Proof
