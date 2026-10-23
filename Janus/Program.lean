import Janus.Arm64.State
import Janus.Arm64.Exec

/-!
# Programs extracted from a Go binary

A `Program` is raw instruction words copied from the binary's `.text` at their virtual
addresses, plus the addresses of runtime stubs that end execution with a named outcome
(e.g. `runtime.panicIndex`). Decoding happens here, in Lean, on every step: the extractor
only copies words and is checked by re-extraction against the binary's SHA-256.
-/

namespace Janus

open Arm64

/-- A contiguous run of instruction words, typically one Go function. -/
structure Segment where
  name : String
  base : Nat
  words : List Nat
deriving Repr, Inhabited

/-- How a known runtime stub ends execution when control reaches its address. -/
inductive StubKind where
  /-- A Go panic (bounds check, nil dereference, divide by zero, explicit `panic`, ...). -/
  | panic
  /-- Stack growth (`runtime.morestack*`); outside the modelled behaviour. -/
  | morestack
deriving Repr, DecidableEq, Inhabited

structure Stub where
  name : String
  addr : Nat
  kind : StubKind
deriving Repr, Inhabited

structure Program where
  segments : List Segment
  stubs : List Stub
  /-- Return address planted in `X30` by the caller; reaching it means the call returned. -/
  exitAddr : Nat
deriving Repr, Inhabited

/-- How a run ends when it does not fault. -/
inductive Outcome where
  | returned (s : State)
  | stub (name : String) (kind : StubKind) (s : State)
deriving Inhabited

namespace Program

def fetchIn : List Segment → Nat → Option Nat
  | [], _ => none
  | seg :: rest, pc =>
    if seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0 then
      match seg.words[(pc - seg.base) / 4]? with
      | some w => some w
      | none => fetchIn rest pc
    else fetchIn rest pc

/-- The instruction word at `pc`, if it lies inside a loaded segment. -/
def fetch (p : Program) (pc : Nat) : Option Nat := fetchIn p.segments pc

def stubAt (p : Program) (pc : Nat) : Option Stub := p.stubs.find? (·.addr = pc)

/-- Run for at most `fuel` instructions. -/
def run (p : Program) : Nat → State → Except Fault Outcome
  | 0, _ => .error .outOfFuel
  | fuel + 1, s =>
    let pc := s.pc.toNat
    if pc = p.exitAddr then .ok (.returned s) else
    match p.stubAt pc with
    | some st => .ok (.stub st.name st.kind s)
    | none =>
      match p.fetch pc with
      | none => .error (.noCode pc)
      | some w => do
        let s' ← Arm64.step w s
        run p fuel s'

end Program
end Janus
