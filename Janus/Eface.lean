/-!
# Interface values of type `any`

A Go `any` value (`eface`, `runtime/runtime2.go`) is two words: the type word (the address of
the dynamic type's `abi.Type` descriptor, `0` for `nil`) and the data word (the value itself for
a pointer-shaped type, otherwise a pointer to it); the layout of `Janus.Spec.Type`. Panic values
are such values (`Janus.GoABI.GoOutcome.panicked`, `Janus.Amd64.GoABI.GoOutcome.panicked`).
Shared by both ISAs.
-/

namespace Janus

/-- An interface value of type `any`: type word and data word. -/
structure Eface where
  typ : Nat
  data : Nat
deriving DecidableEq, Repr, Inhabited

/-- The `nil` interface value. -/
def Eface.nil : Eface := ⟨0, 0⟩

end Janus
