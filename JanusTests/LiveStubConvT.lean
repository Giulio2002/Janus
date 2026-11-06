import Janus
import Janus.Contracts.LiveStubConvT
import Janus.Contracts.LiveStubConvTAmd64

/-! The live `convTstring` / `convT64` (`Janus.Contracts.IfaceLive`) met by stubs in the toy runtime:
the allocating shape (non-empty string, `v ≥ 256`) and the static shape (`""`, `v < 256`). -/

namespace JanusTests.LiveStubConvT.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def tys : Tys := []

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x60000 ∧ ∃ p, args = [p, 5]) ∨ (a = 0x61000 ∧ ∃ p, args = [p, 0]) ∨
  (a = 0x62000 ∧ args = [300]) ∨ (a = 0x63000 ∧ args = [7])

def R : RtInv := toyR tys ok

def linked : Program := P.link [convTstringSeg 0x60000 16, convTstringEmptySeg 0x61000,
  convT64Seg 0x62000 16, convT64SmallSeg 0x63000]

theorem hok_s : ∀ args, ok 0x60000 args → ∃ p, args = [p, 5] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  all_goals (exfalso; omega)

theorem hok_e : ∀ args, ok 0x61000 args → ∃ p, args = [p, 0] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exfalso; omega
  · exact ⟨p, h⟩
  all_goals (exfalso; omega)

theorem hok_6 : ∀ args, ok 0x62000 args → args = [300] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
  · exfalso; omega
  · exfalso; omega
  · exact h
  · exfalso; omega

theorem hok_8 : ∀ args, ok 0x63000 args → args = [7] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact h

set_option maxHeartbeats 4000000 in
theorem cs : RtLiveContract linked 0x60000 4096 R convTstringSpec convTstringLive := by
  janus_live_convtstring 5 16 hok_s

set_option maxHeartbeats 4000000 in
theorem ce : RtLiveContract linked 0x61000 4096 R convTstringSpec convTstringLive := by
  janus_live_convtstring_empty hok_e

set_option maxHeartbeats 4000000 in
theorem c6 : RtLiveContract linked 0x62000 4096 R convT64Spec convT64Live := by
  janus_live_convt64 300 16 hok_6

set_option maxHeartbeats 4000000 in
theorem c8 : RtLiveContract linked 0x63000 4096 R convT64Spec convT64Live := by
  janus_live_convt64_small hok_8

end JanusTests.LiveStubConvT.Arm

namespace JanusTests.LiveStubConvT.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def tys : Tys := []

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x460000 ∧ ∃ p, args = [p, 5]) ∨ (a = 0x461000 ∧ ∃ p, args = [p, 0]) ∨
  (a = 0x462000 ∧ args = [300]) ∨ (a = 0x463000 ∧ args = [7])

def R : RtInv := toyR tys ok

def linked : Janus.Amd64.Program := P.link [convTstringSeg 0x460000 16, convTstringEmptySeg 0x461000,
  convT64Seg 0x462000 16, convT64SmallSeg 0x463000]

theorem hok_s : ∀ args, ok 0x460000 args → ∃ p, args = [p, 5] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  all_goals (exfalso; omega)

theorem hok_e : ∀ args, ok 0x461000 args → ∃ p, args = [p, 0] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exfalso; omega
  · exact ⟨p, h⟩
  all_goals (exfalso; omega)

theorem hok_6 : ∀ args, ok 0x462000 args → args = [300] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
  · exfalso; omega
  · exfalso; omega
  · exact h
  · exfalso; omega

theorem hok_8 : ∀ args, ok 0x463000 args → args = [7] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact h

set_option maxHeartbeats 4000000 in
theorem cs : RtLiveContract64 linked 0x460000 4096 R convTstringSpec convTstringLive := by
  janus64_live_convtstring 5 16 hok_s

set_option maxHeartbeats 4000000 in
theorem ce : RtLiveContract64 linked 0x461000 4096 R convTstringSpec convTstringLive := by
  janus64_live_convtstring_empty hok_e

set_option maxHeartbeats 4000000 in
theorem c6 : RtLiveContract64 linked 0x462000 4096 R convT64Spec convT64Live := by
  janus64_live_convt64 300 16 hok_6

set_option maxHeartbeats 4000000 in
theorem c8 : RtLiveContract64 linked 0x463000 4096 R convT64Spec convT64Live := by
  janus64_live_convt64_small hok_8

end JanusTests.LiveStubConvT.Amd
