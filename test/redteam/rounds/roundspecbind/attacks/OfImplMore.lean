import Extracted

/-!
# Round 15b (red team of round 15, internal calls): attacks beyond audit/roundofimpl

Statement-shape attacks on `Extracted.program.ofImpl impl` / `ImplApart Extracted.program impl`. Controls `c*` verify; attacks `m*` are rejected.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- CONTROL: two identical placement premises. -/
theorem c1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (hap2 : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M1: a raw `Summary` about the runtime's own code with a consumer-chosen (false) specification: not a pinned contract. -/
theorem m1 (impl : List Segment) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hs : Summary (Extracted.program.ofImpl impl) 0x1000 (fun _ => True) (fun _ _ => False)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M2: `ofImpl` of a LINKED program (arg0 not the constant). -/
theorem m2 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract ((Extracted.program.link impl).ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M3: `link` of an `ofImpl` program. -/
theorem m3 (impl : List Segment) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) :
    Ensures ((Extracted.program.ofImpl impl).link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M4: the placement premise through an abbreviation of the consumer (head constant not `ImplApart`). -/
abbrev MyApart (impl : List Segment) : Prop := ImplApart Extracted.program impl
theorem m4 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : MyApart impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M5: the placement premise wrapped in a harmless-looking `Nonempty`/`id`. -/
theorem m5 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : id (ImplApart Extracted.program impl))
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M6: the placement premise as an implication (a conditional constraint). -/
theorem m6 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : impl.length = 0 → ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M7: the contract about `ofImpl impl` at an address that is not the pinned runtime function's. -/
theorem m7 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl) 0 rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M8: the contract about `ofImpl impl` for a runtime function the program does not pin. -/
theorem m8 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.noSuchFunction") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M9: the premise ties `impl` to a second variable that is itself constrained (`impl = impl2`, `impl2` a free list). -/
theorem m9 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (heq : impl = impl2)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M10: a vacuous runtime contract hypothesis next to the placement premise: the contract's state invariant `H` is constrained to be false. -/
theorem m10 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (hH : ∀ a b m x, ¬ H a b m x)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M11: the placement premise AND a premise equating the lengths of impl with rt (a constraint on a runtime variable through another). -/
theorem m11 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (hl : rt.length = impl.length)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M12: `onlySegments` program as the contract's program. -/
theorem m12 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract ((Extracted.program.onlySegments []).ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M13: the statement's program is `onlySegments` (a callee about its own code) instead of Extracted.program. -/
theorem m13 (impl : List Segment) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) :
    Ensures ((Extracted.program.onlySegments []).link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M14: the placement premise's abbreviation ALSO constrains `impl` (its length): a constraint hidden behind a proof-local abbreviation. -/
abbrev BadApart (impl : List Segment) : Prop := ImplApart Extracted.program impl ∧ impl.length = 3
theorem m14 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : BadApart impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M15: the same with a `def` (not reducible). -/
def BadApart2 (impl : List Segment) : Prop := ImplApart Extracted.program impl ∧ impl.length = 3
theorem m15 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : BadApart2 impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M16: a premise that is FALSE for every implementation, hidden in a definition (the theorem is vacuous). -/
def Never (impl : List Segment) : Prop := ImplApart Extracted.program impl ∧ False
theorem m16 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : Never impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- M17: control for the pre-existing round-14 rule (no ofImpl): a premise on `impl` through a definition. -/
def LenThree (impl : List Segment) : Prop := impl.length = 3
theorem m17 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : LenThree impl)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-! ## The rows of audit/roundofimpl whose proof there is `sorry` (blocked there by sorryAx, not necessarily by the shape rule), with real proofs -/
section Shadows
namespace Shadow
/-- A look-alike defined by the consumer: trivially true. -/
def ImplApart (_P : Program) (_impl : List Segment) : Prop := True
theorem s12 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
/-- an opaque predicate: the consumer cannot prove it either way, so a premise on it can be unsatisfiable. -/
opaque OpApart : List Segment → Prop
theorem o1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : OpApart impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
@[irreducible] def Irr (impl : List Segment) : Prop := ImplApart' impl ∧ False
where ImplApart' (impl : List Segment) : Prop := Janus.ImplApart Extracted.program impl
theorem o2 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : Irr impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
/-- A wrapper structure around the real predicate. -/
structure Wrap (impl : List Segment) : Prop where
  h : Janus.ImplApart Extracted.program impl
theorem o4 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : Wrap impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
/-- `PLift` of the real predicate. -/
theorem o5 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : PLift (Janus.ImplApart Extracted.program impl))
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
end Shadow
theorem s13 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program (impl ++ []))
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
theorem s14 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl2)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
theorem s15 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl2)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
theorem s16 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ¬ ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
theorem s17 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ∀ n : Nat, n = n → ImplApart Extracted.program impl)
    (hnew : NewobjectContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim
end Shadows

/-- P1 (pre-existing form, no ofImpl): the contract is about ANOTHER implementation variable's `link`. -/
theorem p1 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl2)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- Q1: the pinned address of `runtime.newobject` with the spec of ANOTHER runtime function (`growslice`): a contract no real implementation satisfies. -/
theorem q1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : RtContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- Q2: the live contract of `growslice` (spec and live data) at the pinned address of `runtime.newobject`. -/
theorem q2 (impl : List Segment) (R : RtInv) (a b : BitVec 64)
    (hnew : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- Q3: a spec and live data of DIFFERENT specs (`wbZeroSpec` with `growsliceLive`). -/
theorem q3 (impl : List Segment) (R : RtInv) (a b : BitVec 64)
    (hnew : RtLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R wbZeroSpec growsliceLive)
    (hap : ImplApart Extracted.program impl) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- Q4: a consumer-defined `LiveSpec` (not an allow-listed constant). -/
def MyLive : LiveSpec := growsliceLive
theorem q4 (impl : List Segment) (R : RtInv) (a b : BitVec 64)
    (hnew : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R growsliceSpec MyLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
