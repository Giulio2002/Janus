import Extracted

/-!
# Round 15c (spec binding): the spec (and live data) of a runtime-contract hypothesis must describe the function it is
stated at, and the contract must be about the implementation the statement runs. Controls `g*`/`n1` verify, attacks are rejected.
Every statement is vacuous on purpose (`fun _ => False` precondition): only the shape of the hypotheses is under test.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- CONTROL: growsliceSpec at runtime.growslice. -/
theorem g1 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- CONTROL: the live contract of growslice at runtime.growslice. -/
theorem g2 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- growsliceBufSpec at runtime.growslice (the spec of `growsliceBuf`). -/
theorem g3 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceBufSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- concatstringSpec 3 at runtime.growslice. -/
theorem g4 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H (concatstringSpec 3)) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- Live data of growsliceBuf with the spec of growslice. -/
theorem g5 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceBufLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- The live contract of growsliceBuf at runtime.growslice. -/
theorem g6 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (R : RtInv) (a b : BitVec 64)
    (h : RtLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceBufSpec growsliceBufLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- N1: the dedicated contract of `newobject` at the address of `growslice`. -/
theorem n1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- D1: the address of `growslice` taken from another program (`onlySegments`), not the extraction's. -/
theorem d1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract (Extracted.program.link impl) ((Extracted.program.onlySegments []).contractAddr "runtime.growslice") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- I1: two contracts, the second about another implementation variable. -/
theorem i1 (impl impl2 : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h1 : RtContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceSpec)
    (h2 : RtContract (Extracted.program.link impl2) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- A consumer-defined `LiveSpec` (not an allow-listed constant) at the right address. -/
def MyLive : LiveSpec := growsliceLive
theorem g7 (impl : List Segment) (R : RtInv) (a b : BitVec 64)
    (h : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec MyLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
