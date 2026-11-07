import Janus
import Janus.Contracts.SbtsLiveSat
import Janus.Contracts.SbtsLiveSatAmd64

/-! U-SBTS-LIVE: the live `slicebytetostring` contract (`RtLiveContract … (slicebytetostringSpec st) slicebytetostringLive`)
met by the `RET` stub for the empty string, at a program's own contract address, on both ISAs; and red team: a request for a
NON-empty string is not met by it. -/

namespace JanusTests.LiveStubSbts.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy

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

end JanusTests.LiveStubSbts.Arm

namespace JanusTests.LiveStubSbts.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy

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

end JanusTests.LiveStubSbts.Amd
