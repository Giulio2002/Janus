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
  /-- A function outside the extracted code whose effect a theorem states as an explicit
  assumption, a *contract* (`runtime.cgocall`, the boundary from Go to C: see `Janus.FFI`).
  The run ends here like at any stub; `Returns` cannot be established through it. Only the
  contract semantics of `Janus.FFI` (`ReturnsC`) continues past it, and only with the contract
  the theorem names. -/
  | external
deriving Repr, DecidableEq, Inhabited

/-- A number for each stub kind (used by the proof automation to read stubs off a program). -/
def StubKind.code : StubKind → Nat
  | .panic => 0
  | .morestack => 1
  | .external => 2

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

/-- A writable global variable as the linker laid it out (`janus extract --global SYM`): the
symbol's address and size and its **link-time image**, the bytes of `.data`/`.noptrdata` the
binary file holds for it (`init`), or none for `.bss`/`.noptrbss` (which the loader zeroes).
Bytes of `[base, base + size)` past `init.length` are zero (`GlobalSegment.byte`). Unlike
`DataSegment`, nothing says memory holds these bytes at a call: the program may have stored
anything there. A theorem that relies on the initial value says so with
`Janus.Spec.GlobalsInit` (docs/PROOFS.md, "Writable globals"). -/
structure GlobalSegment where
  name : String
  base : Nat
  size : Nat
  init : List Nat := []
deriving Repr, Inhabited, DecidableEq

/-- Byte `i` of the global's link-time image (`0` past the file bytes: `.bss`). -/
def GlobalSegment.byte (g : GlobalSegment) (i : Nat) : Nat := g.init.getD i 0

structure Program where
  segments : List Segment
  stubs : List Stub
  /-- Return address planted in `X30` by the caller; reaching it means the call returned.
  The extractor renders a placeholder (`0`). Specifications never use it: they quantify over
  every admissible return address `ret` and run `p.withExit ret` (`GoABI.RetAddr`,
  `GoABI.Ensures`), so a computed branch to a fixed value is never mistaken for a return. -/
  exitAddr : Nat
  data : List DataSegment := []
  /-- Runtime contracts (`janus extract --contract SYM`): functions the extraction calls
  directly but did not copy, as `(name, address)`. The list does not change the run: there is no
  code at these addresses in `segments`, so control reaching one faults with `noCode`. A theorem
  that relies on such a function quantifies over the code at its address (`Program.link`) and
  states the function's behaviour as a hypothesis (a `Tactic.Summary`, see
  docs/RUNTIME-CONTRACTS.md). -/
  contracts : List (String × Nat) := []
  /-- Writable globals named by `janus extract --global SYM`, with their link-time images. Like
  `contracts`, the list does not change the run; `Janus.Spec.GlobalsInit` reads it. -/
  globals : List GlobalSegment := []
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

/-- Memory `m` holds every data segment of `p` at its address, in a well-formed (below `2^48`)
read-only region. Since a store faults on any byte of a read-only region, the data cannot be
overwritten even if a writable region overlaps it. -/
def DataLoaded (p : Program) (m : Arm64.Memory) : Prop :=
  ∀ d ∈ p.data, (m.regions.any fun r => r.base ≤ d.base && d.base + d.bytes.length ≤ r.base + r.size
      && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < d.bytes.length), (m.bytes (d.base + i)).toNat = d.bytes[i]

def stubAt (p : Program) (pc : Nat) : Option Stub := p.stubs.find? (·.addr = pc)

/-- `p` called with return address `ret`: the same code, stubs and data, with the run ending
when `pc` reaches `ret`. -/
def withExit (p : Program) (ret : Nat) : Program := { p with exitAddr := ret }

/-- `p` linked with arbitrary further code `impl` (for example the runtime functions behind its
contracts), placed after `p`'s own segments. Every address where `p` has code still fetches
`p`'s word (`fetch_link`), and stubs, data and the exit address are `p`'s. A theorem about
`p.link impl` for every `impl` satisfying some contract hypotheses is a theorem about the
extracted code together with *any* implementation of the contracts. -/
def link (p : Program) (impl : List Segment) : Program := { p with segments := p.segments ++ impl }

/-- The address of the contract `name` of `p` (`0` if `p` has no such contract). -/
def contractAddr (p : Program) (name : String) : Nat :=
  ((p.contracts.find? (·.1 == name)).map (·.2)).getD 0

theorem fetchIn_append {l₁ : List Segment} (l₂ : List Segment) {pc w : Nat}
    (h : fetchIn l₁ pc = some w) : fetchIn (l₁ ++ l₂) pc = some w := by
  induction l₁ with
  | nil => simp [fetchIn] at h
  | cons seg rest ih =>
    simp only [List.cons_append, fetchIn] at h ⊢
    split
    · rename_i hc
      rw [if_pos hc] at h
      split
      · rename_i w' hw; rw [hw] at h; exact h
      · rename_i hw; rw [hw] at h; exact ih h
    · rename_i hc; rw [if_neg hc] at h; exact ih h

theorem fetch_link {p : Program} (impl : List Segment) {pc w : Nat} (h : p.fetch pc = some w) :
    (p.link impl).fetch pc = some w := fetchIn_append impl h

@[simp] theorem stubAt_link (p : Program) (impl : List Segment) (pc : Nat) :
    (p.link impl).stubAt pc = p.stubAt pc := rfl
@[simp] theorem exitAddr_link (p : Program) (impl : List Segment) :
    (p.link impl).exitAddr = p.exitAddr := rfl
@[simp] theorem data_link (p : Program) (impl : List Segment) :
    (p.link impl).data = p.data := rfl
@[simp] theorem contracts_link (p : Program) (impl : List Segment) :
    (p.link impl).contracts = p.contracts := rfl
@[simp] theorem stubs_link (p : Program) (impl : List Segment) :
    (p.link impl).stubs = p.stubs := rfl
@[simp] theorem globals_link (p : Program) (impl : List Segment) :
    (p.link impl).globals = p.globals := rfl
@[simp] theorem globals_withExit (p : Program) (ret : Nat) :
    (p.withExit ret).globals = p.globals := rfl

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
