import Extracted
/-! ATTACK: a "theorem" that mentions only a named data constant says nothing about the extracted code;
the generated constants do not count as mentioning the program. -/
namespace Proof
theorem noCode : Extracted.dataSize.«example.com/basic.symPows» = 64 := by decide
end Proof
