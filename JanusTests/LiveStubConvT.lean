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


/-! ### Red team -/

/-- a stub that stores the pointer where the length belongs is not a `convTstring` -/
def badLen : List Nat :=
  [0xd2a00809, 0xf9400122, 0x9100004a + 16 * 1024, 0xf900012a, 0xf9000040, 0xf9000440, 0xaa0203e0, 0xd65f03c0]
def linkedBad : Program := P.link [⟨"bad", 0x60000, badLen⟩]

set_option maxHeartbeats 4000000 in
theorem rt_badlen : True := by
  fail_if_success
    have : RtLiveContract linkedBad 0x60000 4096 R convTstringSpec convTstringLive := by
      janus_live_convtstring 5 16 hok_s
  trivial

/-- a stub that advances the bump pointer by less than the box (the next allocation would overlap it) -/
def linkedShort : Program := P.link [convTstringSeg 0x60000 0]

set_option maxHeartbeats 4000000 in
theorem rt_smallbump : True := by
  fail_if_success
    have : RtLiveContract linkedShort 0x60000 4096 R convTstringSpec convTstringLive := by
      janus_live_convtstring 5 0 hok_s
  trivial

/-- the empty string's box holds `(0, 0)`, not `(ptr, 0)`: a spec saying otherwise is not met -/
theorem rt_empty_box_not_ptr (m : Memory) :
    ¬ BoxWords' (toyRt tys) (applyWrites m [(WBUF, 8, 0), (WBUF + 8, 8, 0)]) WBUF [5, 0] := by
  intro h
  have := h.2.2.2 0 (by decide)
  simp only [applyWrites_cons, applyWrites_nil, List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at this
  rw [Memory.readLE_writeLE_of_disjoint _ _ (by simp only [WBUF]; omega), Memory.readLE_writeLE_self] at this
  simp at this

/-- the allocating branches cost something, the static ones nothing and add nothing to the live set -/
example (m : Memory) : 0 < convTstringLive.cost [7, 5] m := convTstringLive_cost_pos _ _ (by decide)
example (m : Memory) : 0 < convT64Live.cost [300] m := convT64Live_cost_pos _ _ (by decide)
example (m : Memory) : convTstringLive.cost [7, 0] m = 0 ∧ liveAdds convTstringLive [7, 0] m 1 2 3 = [] :=
  convTstringLive_empty _ _ 1 2 3 (by decide)
example (m : Memory) : convT64Live.cost [7] m = 0 ∧ liveAdds convT64Live [7] m 1 2 3 = [] :=
  convT64Live_small _ _ 1 2 3 (by decide)

/-- a contract that charges nothing for the allocating branch is a different (wrong) `LiveSpec`:
the framework's lemma `convTstringLive_cost_pos` does not hold of it -/
example : ¬ ∀ (a : List Nat) (m : Memory), arg a 1 ≠ 0 →
    0 < ({ convTstringLive with cost := fun _ _ => 0 } : LiveSpec).cost a m :=
  fun h => by have := h [7, 5] ⟨fun _ => 0, []⟩ (by decide); simp at this

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


/-! ### Red team -/

def badLen : List Nat :=
  [0x41, 0xb9, 0x00, 0x00, 0x40, 0x00, 0x49, 0x8b, 0x11, 0x4c, 0x8d, 0x92] ++ le32 16 ++
  [0x4d, 0x89, 0x11, 0x48, 0x89, 0x02, 0x48, 0x89, 0x42, 0x08, 0x48, 0x89, 0xd0, 0xc3]
def linkedBad : Janus.Amd64.Program := P.link [⟨"bad", 0x460000, badLen⟩]

set_option maxHeartbeats 4000000 in
theorem rt_badlen : True := by
  fail_if_success
    have : RtLiveContract64 linkedBad 0x460000 4096 R convTstringSpec convTstringLive := by
      janus64_live_convtstring 5 16 hok_s
  trivial

def linkedShort : Janus.Amd64.Program := P.link [convTstringSeg 0x460000 0]

set_option maxHeartbeats 4000000 in
theorem rt_smallbump : True := by
  fail_if_success
    have : RtLiveContract64 linkedShort 0x460000 4096 R convTstringSpec convTstringLive := by
      janus64_live_convtstring 5 0 hok_s
  trivial

end JanusTests.LiveStubConvT.Amd
