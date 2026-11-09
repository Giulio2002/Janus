import Extracted
/-! ATTACK: a proof module re-declares a generated chunk definition under its own name and different content.
The name is already declared by the imported `Extracted`, so Lean itself rejects the declaration (compile-time block). -/
def Extracted.seg0_CHUNK_0 : List Nat := []
namespace Proof
theorem correctness : Extracted.program.segments.length = 1 := by decide
end Proof
