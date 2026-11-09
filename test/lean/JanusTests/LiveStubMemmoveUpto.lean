import Janus
import Janus.Contracts.LiveStubMemmoveUpto
import Janus.Contracts.LiveStubMemmoveUptoAmd64

/-! U-MEMMOVE-UPTO (both ISAs): the variable-size live `memmove` stub serves every size `1 … N` (`SetFromDecimal`'s chunks are
`1 … 19` bytes), and a request outside `1 … N` is refused. -/

namespace JanusTests.LiveStubMemmoveUpto.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def linked : Program := P.link [memmoveUptoSeg 0x70000 32]
def ok : Nat → List Nat → Prop := fun a args => a = 0x70000 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32
theorem hok : ∀ args, ok 0x70000 args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32 := fun _ h => h.2

set_option maxHeartbeats 16000000 in
theorem mv32 : MemmoveLive linked 0x70000 4096 (toyR [] ok) := by
  janus_live_memmove_upto 32 hok

-- red team: a request for MORE than N bytes (here 33, or any k up to 40) is not served by the N = 32 stub
def okBig : Nat → List Nat → Prop := fun a args => a = 0x70000 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 40
set_option maxHeartbeats 16000000 in
theorem rt_over_N : True := by
  fail_if_success
    have : MemmoveLive linked 0x70000 4096 (toyR [] okBig) := by
      janus_live_memmove_upto 40 (fun _ h => h.2)
  trivial

-- red team: a request for 0 bytes is outside the stub's range (the hypothesis must say 1 ≤ k)
def okZero : Nat → List Nat → Prop := fun a args => a = 0x70000 ∧ ∃ q p k, args = [q, p, k] ∧ 0 ≤ k ∧ k ≤ 32
set_option maxHeartbeats 16000000 in
theorem rt_zero : True := by
  fail_if_success
    have : MemmoveLive linked 0x70000 4096 (toyR [] okZero) := by
      janus_live_memmove_upto 32 (fun _ h => h.2)
  trivial

end JanusTests.LiveStubMemmoveUpto.Arm

namespace JanusTests.LiveStubMemmoveUpto.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def linked : Janus.Amd64.Program := P.link [memmoveUptoSeg64 0x470000 32]
def ok : Nat → List Nat → Prop := fun a args => a = 0x470000 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32
theorem hok : ∀ args, ok 0x470000 args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 32 := fun _ h => h.2

set_option maxHeartbeats 16000000 in
theorem mv32 : MemmoveLive64 linked 0x470000 4096 (toyR [] ok) := by
  janus64_live_memmove_upto 32 hok

-- red team: more than N bytes is refused
def okBig : Nat → List Nat → Prop := fun a args => a = 0x470000 ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 40
set_option maxHeartbeats 16000000 in
theorem rt_over_N : True := by
  fail_if_success
    have : MemmoveLive64 linked 0x470000 4096 (toyR [] okBig) := by
      janus64_live_memmove_upto 40 (fun _ h => h.2)
  trivial

end JanusTests.LiveStubMemmoveUpto.Amd
