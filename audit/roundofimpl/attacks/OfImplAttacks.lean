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

end Proof
