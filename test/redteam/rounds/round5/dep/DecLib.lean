/-! Round 5 dependency fixture (E1h/E3e): a pinned git dependency carrying a custom
high-priority `Decidable` instance, a class-valued def, a plain def whose body uses the
instance, and a structure with a field named like Janus's `regs`. -/
namespace DecLib

/-- A custom `Decidable` instance (priority high, so it wins over `instDecidableEqBitVec`). -/
instance (priority := high) evilDec (x : BitVec 64) : Decidable (x = 0) :=
  if h : x.toNat = 0 then .isTrue (BitVec.eq_of_toNat_eq (by simpa using h))
  else .isFalse (fun e => h (by simp [e]))

/-- The same as a plain def: class-valued. -/
def myDec (x : BitVec 64) : Decidable (x = 0) := evilDec x

/-- A plain def whose body runs `decide` with the instance above. -/
def isZero (x : BitVec 64) : Bool := decide (x = 0)

/-- A structure with a field named like `Janus.Arm64.State.regs`. -/
structure View where
  regs : Nat → BitVec 64

def View.ofFun (f : Nat → BitVec 64) : View := ⟨f⟩

end DecLib
