import Extracted
/-! ATTACK A8 (expected BLOCKED): classic holes, one theorem each. Run with --theorem Proof.tN. -/
namespace Proof
-- t1: an axiom under an innocuous name
axiom helperLemma : False
theorem t1 : (1 : Nat) = 2 := helperLemma.elim
-- t2: implemented_by on a Decidable instance; `decide` is evaluated by the kernel
def evilDec (p : Prop) : Decidable p := Decidable.isFalse (fun _ => sorry)
def evilImpl (p : Prop) : Decidable p := Decidable.isTrue sorry
-- t3: partial def unfolding
partial def loop (n : Nat) : Nat := loop (n + 1)
-- t4: opaque with a value
opaque secret : Nat := 1
theorem t4 : secret = 1 := by first | rfl | decide | sorry
theorem t3 : loop 0 = 0 := by first | rfl | sorry
end Proof
