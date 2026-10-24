import Janus.Program
import Janus.Amd64.Exec

/-!
# amd64 programs extracted from a Go binary

An `Amd64.Program` is raw instruction **bytes** copied from the binary's `.text` at their
virtual addresses (one `Segment` per function), plus the runtime stubs that end execution with
a named outcome and the read-only data the code loads. It reuses the ISA-independent
`Janus.Stub`, `Janus.StubKind` and `Janus.DataSegment`. Decoding happens here, in Lean, on
every step: `fetch` returns the (at most 15) bytes from `rip` to the end of its segment and
`Amd64.step` decodes them. An instruction that would extend past the end of its segment is
undecodable (it is never stitched together from two segments).
-/

namespace Janus.Amd64

/-- A contiguous run of code bytes, typically one Go function. -/
structure Segment where
  name : String
  base : Nat
  bytes : List Nat
deriving Repr, Inhabited

structure Program where
  segments : List Segment
  stubs : List Janus.Stub
  /-- Return address planted at `[RSP]` by the caller; reaching it means the call returned.
  The extractor renders a placeholder; specifications quantify over every admissible return
  address `ret` and run `p.withExit ret` (`GoABI.RetAddr`, `GoABI.Ensures`). -/
  exitAddr : Nat
  data : List Janus.DataSegment := []
  /-- Runtime contracts (`janus extract --contract SYM`): functions called directly but not
  copied, as `(name, address)`. They do not change the run (no code there: `noCode`); see
  `Janus.Program.contracts` and docs/RUNTIME-CONTRACTS.md. -/
  contracts : List (String × Nat) := []
deriving Repr, Inhabited

/-- How a run ends when it does not fault. -/
inductive Outcome where
  | returned (s : State)
  | stub (name : String) (kind : Janus.StubKind) (s : State)
deriving Inhabited

namespace Program

/-- The bytes from `pc` to the end of the first segment containing `pc`, at most 15. -/
def fetchIn : List Segment → Nat → Option (List Nat)
  | [], _ => none
  | seg :: rest, pc =>
    if seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length then
      some ((seg.bytes.drop (pc - seg.base)).take 15)
    else fetchIn rest pc

/-- The instruction bytes at `pc`, if it lies inside a loaded segment. -/
def fetch (p : Program) (pc : Nat) : Option (List Nat) := fetchIn p.segments pc

/-- Memory `m` holds every data segment of `p` at its address, in a well-formed (below `2^48`)
read-only region (which no store can modify, see `Janus.Arm64.Memory.accessible`). -/
def DataLoaded (p : Program) (m : Memory) : Prop :=
  ∀ d ∈ p.data, (m.regions.any fun r => r.base ≤ d.base && d.base + d.bytes.length ≤ r.base + r.size
      && r.base + r.size ≤ 2 ^ 48 && !r.writable) = true ∧
    ∀ i (h : i < d.bytes.length), (m.bytes (d.base + i)).toNat = d.bytes[i]

def stubAt (p : Program) (pc : Nat) : Option Janus.Stub := p.stubs.find? (·.addr = pc)

/-- `p` called with return address `ret`: the same code, stubs and data, with the run ending
when `rip` reaches `ret`. -/
def withExit (p : Program) (ret : Nat) : Program := { p with exitAddr := ret }

/-- `p` linked with arbitrary further code `impl`, after `p`'s own segments (see
`Janus.Program.link`): every address where `p` has code still fetches `p`'s bytes. -/
def link (p : Program) (impl : List Segment) : Program := { p with segments := p.segments ++ impl }

/-- The address of the contract `name` of `p` (`0` if `p` has no such contract). -/
def contractAddr (p : Program) (name : String) : Nat :=
  ((p.contracts.find? (·.1 == name)).map (·.2)).getD 0

theorem fetchIn_append {l₁ : List Segment} (l₂ : List Segment) {pc : Nat} {bs : List Nat}
    (h : fetchIn l₁ pc = some bs) : fetchIn (l₁ ++ l₂) pc = some bs := by
  induction l₁ with
  | nil => simp [fetchIn] at h
  | cons seg rest ih =>
    simp only [List.cons_append, fetchIn] at h ⊢
    split
    · rename_i hc; rw [if_pos hc] at h; exact h
    · rename_i hc; rw [if_neg hc] at h; exact ih h

theorem fetch_link {p : Program} (impl : List Segment) {pc : Nat} {bs : List Nat}
    (h : p.fetch pc = some bs) : (p.link impl).fetch pc = some bs := fetchIn_append impl h

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

/-- Run for at most `fuel` instructions. -/
def run (p : Program) : Nat → State → Except Fault Outcome
  | 0, _ => .error .outOfFuel
  | fuel + 1, s =>
    let pc := s.rip.toNat
    if pc = p.exitAddr then .ok (.returned s) else
    match p.stubAt pc with
    | some st => .ok (.stub st.name st.kind s)
    | none =>
      match p.fetch pc with
      | none => .error (.noCode pc)
      | some bs => do
        let s' ← Amd64.step bs s
        run p fuel s'

end Program
end Janus.Amd64
