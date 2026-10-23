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

/-- Read-only data copied from the binary (e.g. `.rodata` constants the code loads). It is
not executable; a call's precondition states that memory holds these bytes read-only
(`Program.DataLoaded`). -/
structure DataSegment where
  name : String
  base : Nat
  bytes : List Nat
deriving Repr, Inhabited

structure Program where
  segments : List Segment
  stubs : List Stub
  /-- Return address planted in `X30` by the caller; reaching it means the call returned. -/
  exitAddr : Nat
  data : List DataSegment := []
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

/-- Memory `m` holds every data segment of `p` at its address, in a read-only region. -/
def DataLoaded (p : Program) (m : Arm64.Memory) : Prop :=
  ∀ d ∈ p.data, (m.regions.any fun r => r.base ≤ d.base && d.base + d.bytes.length ≤ r.base + r.size
      && !r.writable) = true ∧
    ∀ i (h : i < d.bytes.length), (m.bytes (d.base + i)).toNat = d.bytes[i]

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
