import Extracted

/-! Spec binding on amd64: the same spec-binding rows. `h1` verifies, the others are rejected. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

/-- CONTROL. -/
theorem h1 (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- growsliceBufSpec at runtime.growslice. -/
theorem h2 (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceBufSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- The newobject contract at growslice. -/
theorem h3 (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

/-- About another implementation variable. -/
theorem h4 (impl impl2 : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (h : RtContract64 (Extracted.program.link impl2) (Extracted.program.contractAddr "runtime.growslice") rt 4096 H growsliceSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
