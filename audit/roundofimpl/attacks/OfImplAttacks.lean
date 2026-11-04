import Extracted

/-!
# Round 15 (internal calls): `Extracted.program.ofImpl impl` and `ImplApart Extracted.program impl`

A runtime contract may be assumed about the runtime's own code, `Extracted.program.ofImpl impl` (no user
code), with the same discipline as `Extracted.program.link impl`: `impl` a variable of the statement,
mentioned only inside `link`/`ofImpl`, constrained by nothing but the pinned contracts, the model laws and
the one premise `ImplApart Extracted.program impl` ("the runtime's code does not overlap the extracted
function's code"). Controls verify (`ctl*`); every attack is rejected (`r*`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

def Impl0 : List Segment := []

/-- CONTROL: a contract about the runtime's own code. -/
theorem ctl1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- CONTROL: with the placement premise, in exactly its form. -/
theorem ctl2 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- CONTROL: hypotheses over `link` and over `ofImpl` for the same `impl`. -/
theorem ctl3 (impl : List Segment) (rt rt' : List (Nat × Nat)) (H H' : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (h1 : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (h2 : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt' 4096 H') :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- R1: a contract about the runtime code of a CONCRETE implementation. -/
theorem r1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.ofImpl Impl0)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R2: `impl` is constrained by a premise (its length) next to an `ofImpl` contract. -/
theorem r2 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : impl.length = 3)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R3: a premise constraining the runtime through a function of the `ofImpl` program. -/
theorem r3 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : (Extracted.program.ofImpl impl).exitAddr = 0)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R4: `ofImpl` of a program other than `Extracted.program`. -/
theorem r4 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract ((Extracted.program.withExit 5).ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R5: `ofImpl` as the program of a statement about the extracted function. -/
theorem r5 (impl : List Segment) (a b : BitVec 64) :
    Ensures (Extracted.program.ofImpl impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R6: the placement predicate about another program. -/
theorem r6 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart (Extracted.program.withExit 5) impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R7: a different predicate (part of what `ImplApart` says). -/
theorem r7 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : List.Pairwise Segment.Apart (Extracted.program.segments ++ impl))
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R8: the placement predicate combined with another constraint in one premise. -/
theorem r8 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl ∧ impl.length = 3)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R9: the placement predicate and, in a second premise, another constraint. -/
theorem r9 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (h : impl.length = 3)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R10: the placement predicate as a precondition of the conclusion, not a premise. -/
theorem r10 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun _ => ImplApart Extracted.program impl) (fun _ _ => True) := sorry

/-- R11: the placement predicate for a CONCRETE implementation next to a link hypothesis. -/
theorem r11 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program Impl0)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- CONTROL: the placement premise may come after the contract (position is irrelevant). -/
theorem ctl4 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hap : ImplApart Extracted.program impl) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

namespace Shadow
/-- A look-alike defined by the consumer that states nothing (`True`): harmless, so accepted. -/
def ImplApart (_P : Program) (_impl : List Segment) : Prop := True

/-- CONTROL: the consumer's own `ImplApart`, which constrains nothing. -/
theorem ctl7 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
end Shadow

namespace Shadow2
/-- A look-alike that constrains the runtime: it is not the trusted predicate. -/
def ImplApart (_P : Program) (impl : List Segment) : Prop := impl.length = 3

/-- R12: the consumer's own `ImplApart`, which constrains `impl`. -/
theorem r12 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry
end Shadow2

/-- R13: the placement predicate about a term built from `impl`, not the variable. -/
theorem r13 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program (impl ++ []))
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- CONTROL: the placement premise for another variable than the statement's (it constrains nothing the statement is about). -/
theorem ctl9 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl2)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- CONTROL: a contract about another variable's runtime code (it constrains nothing the statement is about; the Witness must still exhibit it). -/
theorem ctl10 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl2)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- R16: the negated placement predicate. -/
theorem r16 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ¬ ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R17: the placement predicate under a quantifier. -/
theorem r17 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ∀ n : Nat, n = n → ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R18: the placement premise is the only mention of `impl` outside link/ofImpl but the statement
program is `ofImpl`'s sibling with extra segments (`link` of an appended list). -/
theorem r18 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl (impl ++ Impl0))
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- CONTROL: the placement premise as an implicit binder (still a hypothesis of the statement). -/
theorem ctl5 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    {hap : ImplApart Extracted.program impl}
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A consumer-defined wrapper that unfolds to the placement predicate. -/
def MyApart (impl : List Segment) : Prop := ImplApart Extracted.program impl

/-- CONTROL: a consumer-defined wrapper that unfolds to the placement predicate itself. -/
theorem ctl8 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : MyApart impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- R20: the placement predicate about the runtime's own program (not `Extracted.program`). -/
theorem r20 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart (Extracted.program.ofImpl impl) impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

/-- R21: `impl` constrained through the placement predicate's program argument (`Extracted.program` with
the runtime's segments appended is not `Extracted.program`). -/
theorem r21 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart { Extracted.program with segments := Extracted.program.segments ++ impl } impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := sorry

end Proof
