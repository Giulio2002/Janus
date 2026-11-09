import Extracted

/-!
Round 15a: ways to assume a runtime contract without the statement's `ContractHyps` showing it.
Every theorem below is VACUOUS (it assumes `PLift False`, or a contract that nothing can satisfy) and
assumes `NewobjectContract`; none of them may be accepted without a non-vacuity witness.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

def pairType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "example.com/basic.NewPair" 8)
    (segWord Extracted.program "example.com/basic.NewPair" 9) 0

/-- C1 control: the contract is a Prop hypothesis (as `correctness`), plus an absurd premise. -/
theorem ctl (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : False)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun s s' => s'.pc = s.pc) :=
  hF.elim

/-- C2: the contract hypothesis lives in a `PLift` binder (a `Type`, not a `Prop`). -/
theorem plift (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : False)
    (hnew : PLift (NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun s s' => s'.pc = s.pc) :=
  hF.elim

/-- C3: a `Subtype` binder. -/
theorem sub (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : False)
    (hnew : { u : Unit // NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H }) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun s s' => s'.pc = s.pc) :=
  hF.elim

/-- C4: the absurd premise as a `PLift` too, the contract as a `Nonempty`. -/
theorem nonempty (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : PLift False)
    (hnew : Nonempty (PLift (NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H))) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun s s' => s'.pc = s.pc) :=
  hF.down.elim

/-- C5: the contract assumed inside the precondition lambda of `Ensures`. -/
theorem inpre (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : False) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0 ∧ ¬ NewobjectContract (Extracted.program.link impl)
        (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
      (fun s s' => s'.pc = s.pc) :=
  hF.elim

/-- C6: the contract is a conclusion implication (an `→` inside an `∧`, not leading). -/
theorem inconc (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hF : False) :
    (NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H →
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => GuardOK s 0) (fun s s' => s'.pc = s.pc)) :=
  hF.elim

end Proof
