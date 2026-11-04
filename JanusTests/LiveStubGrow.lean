import Janus
import Janus.Contracts.LiveStubGrow
import Janus.Contracts.LiveStubGrowAmd64

/-! The `growslice` stub (`Janus.Contracts.LiveStubGrow`): element size 1 (bytes), an allocation of
5 bytes (no old elements) and a growth from 8 to 16 elements that copies the 8 old bytes. -/

namespace JanusTests.LiveStubGrow.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

/-- `[]byte` at `0x30000`: size 1, no pointers. -/
def tys : Tys := [(0x30000, 1, 0)]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x60000 ∧ ∃ p, args = [p, 5, 0, 5, 0x30000]) ∨ (a = 0x61000 ∧ ∃ p, args = [p, 9, 8, 1, 0x30000])

def R : RtInv := toyR tys ok

-- nextslicecap 5 0 = 5, roundupsize 5 = 8: cap 8, no copy; then 9 / 8: 16, copy 8 bytes
def linked : Program := P.link [growsliceSeg 0x60000 0 16 8, growsliceSeg 0x61000 8 16 16]

theorem hok1 : ∀ args, ok 0x60000 args → ∃ p, args = [p, 5, 0, 5, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  · exfalso; omega

theorem hok2 : ∀ args, ok 0x61000 args → ∃ p, args = [p, 9, 8, 1, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩
  · exfalso; omega
  · exact ⟨p, h⟩

theorem g1 : RtLiveContract linked 0x60000 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 5 0 5 16 8 hok1

theorem g2 : RtLiveContract linked 0x61000 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 9 8 1 16 16 hok2

end JanusTests.LiveStubGrow.Arm

namespace JanusTests.LiveStubGrow.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }

def tys : Tys := [(0x30000, 1, 0)]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x460000 ∧ ∃ p, args = [p, 5, 0, 5, 0x30000]) ∨ (a = 0x461000 ∧ ∃ p, args = [p, 9, 8, 1, 0x30000])

def R : RtInv := toyR tys ok

def linked : Janus.Amd64.Program := P.link [growsliceSeg 0x460000 0 16 8, growsliceSeg 0x461000 8 16 16]

theorem hok1 : ∀ args, ok 0x460000 args → ∃ p, args = [p, 5, 0, 5, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  · exfalso; omega

theorem hok2 : ∀ args, ok 0x461000 args → ∃ p, args = [p, 9, 8, 1, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩
  · exfalso; omega
  · exact ⟨p, h⟩

theorem g1 : RtLiveContract64 linked 0x460000 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (0x30000, 1, 0) 5 0 5 16 8 hok1

theorem g2 : RtLiveContract64 linked 0x461000 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (0x30000, 1, 0) 9 8 1 16 16 hok2

end JanusTests.LiveStubGrow.Amd
