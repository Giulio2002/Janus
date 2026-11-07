import Janus
import Janus.Contracts.SbtsLiveSat
import Janus.Contracts.SbtsLiveSatAmd64
import Janus.Contracts.LiveStubSbts
import Janus.Contracts.LiveStubSbtsAmd64

/-! U-SBTS-LIVE: the live `slicebytetostring` contract (`RtLiveContract … (slicebytetostringSpec st) slicebytetostringLive`)
met by the `RET` stub for the empty string, at a program's own contract address, on both ISAs; and red team: a request for a
NON-empty string is not met by it. -/

namespace JanusTests.LiveStubSbts.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def ok : Nat → List Nat → Prop := fun a args => a = 0x60000 ∧ args = [0, 0, 0]
def okBad : Nat → List Nat → Prop := fun a args => a = 0x60000 ∧ args = [0, 0x30000, 5]
def linked : Program := P.link [⟨"sbts", 0x60000, [0xd65f03c0]⟩]

theorem hok : ∀ args, ok 0x60000 args → args = [0, 0, 0] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem sb0 (st : Nat) : RtLiveContract linked 0x60000 4096 (toyR [] ok) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts_empty hok

/-- the `RET` stub is only for the empty string: the premise `args = [0, 0, 0]` of the tactic is false for a request for a
5-byte string, so the tactic cannot be used for one -/
theorem rt_nonempty : ¬ ∀ args, okBad 0x60000 args → args = [0, 0, 0] := by
  intro h
  have := h [0, 0x30000, 5] ⟨rfl, rfl⟩
  simp at this

/-! ### Non-empty strings: a copy into a fresh block (`buf = 0`, `n` a size class) -/

def okC : Nat → List Nat → Prop := fun a args =>
  (a = 0x61000 ∧ ∃ ptr, args = [0, ptr, 16]) ∨ (a = 0x62000 ∧ ∃ ptr, args = [0, ptr, 32]) ∨
  (a = 0x63000 ∧ ∃ ptr, args = [0, ptr, 48])
def linkedC : Program := P.link [sbtsSeg 0x61000 16 16, sbtsSeg 0x62000 32 32, sbtsSeg 0x63000 48 48]

theorem hokC16 : ∀ args, okC 0x61000 args → ∃ ptr, args = [0, ptr, 16] := by
  intro args h; rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals (exfalso; revert h; decide)
theorem hokC32 : ∀ args, okC 0x62000 args → ∃ ptr, args = [0, ptr, 32] := by
  intro args h; rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; exfalso; revert h; decide; exact h; exfalso; revert h; decide
theorem hokC48 : ∀ args, okC 0x63000 args → ∃ ptr, args = [0, ptr, 48] := by
  intro args h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; exfalso; revert h; decide; exfalso; revert h; decide; exact h

set_option maxHeartbeats 4000000 in
theorem sb16 (st : Nat) : RtLiveContract linkedC 0x61000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts 16 16 hokC16
set_option maxHeartbeats 4000000 in
theorem sb32 (st : Nat) : RtLiveContract linkedC 0x62000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts 32 32 hokC32
set_option maxHeartbeats 4000000 in
theorem sb48 (st : Nat) : RtLiveContract linkedC 0x63000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts 48 48 hokC48

-- red team: a length that is not a size class (`roundupsize 20 true = 24`: the block the contract adds to the live set is not the
-- block the allocator hands out) is refused
set_option maxHeartbeats 4000000 in
theorem rt_notclass (st : Nat) : True := by
  fail_if_success
    have : RtLiveContract linkedC 0x61000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
      janus_live_sbts 20 32 hokC16
  trivial

-- red team: a bump advance smaller than the block (the next allocation would overlap it) is refused
set_option maxHeartbeats 4000000 in
theorem rt_smallA (st : Nat) : True := by
  fail_if_success
    have : RtLiveContract linkedC 0x61000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
      janus_live_sbts 16 0 hokC16
  trivial


/-! ### n > 32 with ANY caller buffer (FV-J2: wrappers always pass a stack buffer) -/

def okB : Nat → List Nat → Prop := fun a args => a = 0x64000 ∧ ∃ buf ptr, args = [buf, ptr, 48]
def linkedB : Program := P.link [sbtsSeg 0x64000 48 48]
theorem hokB : ∀ args, okB 0x64000 args → ∃ buf ptr, args = [buf, ptr, 48] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem sbBig48 (st : Nat) : RtLiveContract linkedB 0x64000 4096 (toyR [] okB) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts_big 48 48 hokB

-- red team: the big variant is for n > 32 only (for n <= 32 a non-nil buffer is used, not a fresh block)
set_option maxHeartbeats 4000000 in
theorem rt_big_small (st : Nat) : True := by
  fail_if_success
    have : RtLiveContract (P.link [sbtsSeg 0x65000 16 16]) 0x65000 4096 (toyR [] (fun a args => a = 0x65000 ∧ ∃ buf ptr, args = [buf, ptr, 16]))
        (slicebytetostringSpec st) slicebytetostringLive := by
      janus_live_sbts_big 16 16 (fun _ h => h.2)
  trivial

end JanusTests.LiveStubSbts.Arm

namespace JanusTests.LiveStubSbts.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def ok : Nat → List Nat → Prop := fun a args => a = 0x460000 ∧ args = [0, 0, 0]
def okBad : Nat → List Nat → Prop := fun a args => a = 0x460000 ∧ args = [0, 0x30000, 5]
def linked : Janus.Amd64.Program := P.link [⟨"sbts", 0x460000, [0xc3]⟩]

theorem hok : ∀ args, ok 0x460000 args → args = [0, 0, 0] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem sb0 (st : Nat) : RtLiveContract64 linked 0x460000 4096 (toyR [] ok) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts_empty hok

theorem rt_nonempty : ¬ ∀ args, okBad 0x460000 args → args = [0, 0, 0] := by
  intro h
  have := h [0, 0x30000, 5] ⟨rfl, rfl⟩
  simp at this

/-! ### Non-empty strings: a copy into a fresh block (`buf = 0`, `n` a size class) -/

def okC : Nat → List Nat → Prop := fun a args =>
  (a = 0x4661000 ∧ ∃ ptr, args = [0, ptr, 16]) ∨ (a = 0x4662000 ∧ ∃ ptr, args = [0, ptr, 32]) ∨
  (a = 0x4663000 ∧ ∃ ptr, args = [0, ptr, 48])
def linkedC : Janus.Amd64.Program := P.link [sbtsSeg64 0x4661000 16 16, sbtsSeg64 0x4662000 32 32, sbtsSeg64 0x4663000 48 48]

theorem hokC16 : ∀ args, okC 0x4661000 args → ∃ ptr, args = [0, ptr, 16] := by
  intro args h; rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩; exact h; all_goals (exfalso; revert h; decide)
theorem hokC32 : ∀ args, okC 0x4662000 args → ∃ ptr, args = [0, ptr, 32] := by
  intro args h; rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩; exfalso; revert h; decide; exact h; exfalso; revert h; decide
theorem hokC48 : ∀ args, okC 0x4663000 args → ∃ ptr, args = [0, ptr, 48] := by
  intro args h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩; exfalso; revert h; decide; exfalso; revert h; decide; exact h

set_option maxHeartbeats 4000000 in
theorem sb16 (st : Nat) : RtLiveContract64 linkedC 0x4661000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts 16 16 hokC16
set_option maxHeartbeats 4000000 in
theorem sb32 (st : Nat) : RtLiveContract64 linkedC 0x4662000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts 32 32 hokC32
set_option maxHeartbeats 4000000 in
theorem sb48 (st : Nat) : RtLiveContract64 linkedC 0x4663000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts 48 48 hokC48

-- red team: a length that is not a size class (`roundupsize 20 true = 24`: the block the contract adds to the live set is not the
-- block the allocator hands out) is refused
set_option maxHeartbeats 4000000 in
theorem rt_notclass (st : Nat) : True := by
  fail_if_success
    have : RtLiveContract64 linkedC 0x4661000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
      janus64_live_sbts 20 32 hokC16
  trivial

-- red team: a bump advance smaller than the block (the next allocation would overlap it) is refused
set_option maxHeartbeats 4000000 in
theorem rt_smallA (st : Nat) : True := by
  fail_if_success
    have : RtLiveContract64 linkedC 0x4661000 4096 (toyR [] okC) (slicebytetostringSpec st) slicebytetostringLive := by
      janus64_live_sbts 16 0 hokC16
  trivial


/-! ### n > 32 with ANY caller buffer -/

def okB : Nat → List Nat → Prop := fun a args => a = 0x4664000 ∧ ∃ buf ptr, args = [buf, ptr, 48]
def linkedB : Janus.Amd64.Program := P.link [sbtsSeg64 0x4664000 48 48]
theorem hokB : ∀ args, okB 0x4664000 args → ∃ buf ptr, args = [buf, ptr, 48] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem sbBig48 (st : Nat) : RtLiveContract64 linkedB 0x4664000 4096 (toyR [] okB) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts_big 48 48 hokB

end JanusTests.LiveStubSbts.Amd

/-! U-SBTS-STATIC: the identity table. -/
namespace JanusTests.LiveStubSbts.Static
open Janus Janus.Arm64 Janus.Contracts
-- the byte of `staticuint64s[b]` is `b` given the table; a memory of zeros is a counterexample without it
example (st : Nat) (m : Memory) (h : StaticTable st m) : Janus.Spec.strBytes m (st + 8 * 7) 1 = [7] := h.strBytes (by decide)
example (st : Nat) : ¬ ∀ m : Memory, Janus.Spec.strBytes m (st + 8 * 1) 1 = [1] := sbts_n1_needs_table st
end JanusTests.LiveStubSbts.Static
