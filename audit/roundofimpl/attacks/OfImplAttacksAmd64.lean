import Extracted

/-! Round 15, amd64: the same controls and the main attacks for the amd64 forms
(`Janus.Amd64.Program.ofImpl`, `Janus.Amd64.ImplApart`). See `OfImplAttacks.lean`. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Proof

def Impl0 : List Janus.Amd64.Segment := []

theorem ctl1 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl)
    (hnew : NewobjectContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem ctl2 (impl : List Janus.Amd64.Segment) (rt rt' : List (Nat × Nat)) (H H' : RtReady) (a b : BitVec 64)
    (h1 : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (h2 : NewobjectContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt' 4096 H') :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem r1 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.ofImpl Impl0)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem r8 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl ∧ impl.length = 3)
    (hnew : NewobjectContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem r6 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart (Extracted.program.withExit 5) impl)
    (hnew : NewobjectContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem r9 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (a b : BitVec 64)
    (hap : ImplApart Extracted.program impl) (h : impl.length = 3)
    (hnew : NewobjectContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

theorem r5 (impl : List Janus.Amd64.Segment) (a b : BitVec 64) :
    Ensures (Extracted.program.ofImpl impl) Extracted.entry [a, b] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs hp; exact hp.elim

end Proof
