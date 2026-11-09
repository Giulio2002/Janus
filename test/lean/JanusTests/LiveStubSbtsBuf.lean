import Janus
import Janus.Contracts.LiveStubSbtsAmd64

/-! U-SBTS-LIVE: the empty string with ANY caller buffer (the real wrappers always pass a stack buffer). -/
namespace JanusTests.LiveStubSbtsBuf.Arm
open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub
def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def ok : Nat → List Nat → Prop := fun a args => a = 0x60000 ∧ ∃ buf p, args = [buf, p, 0]
def linked : Program := P.link [⟨"sbts", 0x60000, [0xaa0203e1, 0xd65f03c0]⟩]
theorem hok : ∀ args, ok 0x60000 args → ∃ buf p, args = [buf, p, 0] := fun _ h => h.2
set_option maxHeartbeats 4000000 in
theorem sb0buf (st : Nat) : RtLiveContract linked 0x60000 4096 (toyR [] ok) (slicebytetostringSpec st) slicebytetostringLive := by
  janus_live_sbts_empty_buf hok
end JanusTests.LiveStubSbtsBuf.Arm

namespace JanusTests.LiveStubSbtsBuf.Amd
open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy
def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def ok : Nat → List Nat → Prop := fun a args => a = 0x460000 ∧ ∃ buf p, args = [buf, p, 0]
def linked : Janus.Amd64.Program := P.link [⟨"sbts", 0x460000, [0x48, 0x89, 0xcb, 0xc3]⟩]
theorem hok : ∀ args, ok 0x460000 args → ∃ buf p, args = [buf, p, 0] := fun _ h => h.2
set_option maxHeartbeats 4000000 in
theorem sb0buf (st : Nat) : RtLiveContract64 linked 0x460000 4096 (toyR [] ok) (slicebytetostringSpec st) slicebytetostringLive := by
  janus64_live_sbts_empty_buf hok
end JanusTests.LiveStubSbtsBuf.Amd
