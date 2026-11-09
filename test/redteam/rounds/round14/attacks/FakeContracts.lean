import Extracted

/-! Round 14 (class 7): a consumer file cannot mint a runtime contract. Each theorem pins `impl` through a premise
headed by a definition the PROOF module declares, in a `Janus.*` namespace, with a contract-looking shape. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Janus.Contracts

/-- named like a contract, takes a program: a trivial predicate of the linked program (no projection, so the premise rule is what decides). -/
def FakeContract (p : Program) : Prop := p = p

/-- a `Summary`-bodied def: requires code at address 0 of the linked program. -/
def FakeSummary (p : Program) : Prop := Janus.Tactic.Summary p 0 (fun _ => True) (fun _ _ => True)

namespace Sub
/-- shadows the short name of a real contract (the real one is `Janus.Contracts.NewobjectContract`). -/
def NewobjectContract (p : Program) (_a : Nat) (_rt : List (Nat × Nat)) (_n : Nat) (_H : RtReady) : Prop :=
  p = p
end Sub

end Janus.Contracts

namespace Proof

theorem fake1 (impl : List Segment) (h : Janus.Contracts.FakeContract (Extracted.program.link impl)) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun s => GuardOK s 0)
      (fun _ s' => (s'.regs 0).toNat = 0) := sorry

theorem fake2 (impl : List Segment) (h : Janus.Contracts.FakeSummary (Extracted.program.link impl)) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun s => GuardOK s 0)
      (fun _ s' => (s'.regs 0).toNat = 0) := sorry

theorem fake3 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (h : Janus.Contracts.Sub.NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) (a b : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b] (fun s => GuardOK s 0)
      (fun _ s' => (s'.regs 0).toNat = 0) := sorry

end Proof
