/-! Round 7 dependency fixture (J1): a pinned git dependency whose def name and docstring say
one thing while its body says another. -/
namespace MisLib

/-- The product `a * b` of two 64-bit words, wrapped to 64 bits. -/
def mul (a b : BitVec 64) : BitVec 64 := a + b

end MisLib
