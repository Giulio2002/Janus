import Janus

/-! The `memmove` / `memclrNoHeapPointers` stubs (`Janus.Contracts.LiveStubSlice`) at addresses other
than the toy's, for requests of several sizes (words and 4, 2, 1-byte tails). -/

namespace JanusTests.LiveStubSlice.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

def linked : Program := P.link [memmoveSeg 0x50000 12, memclrSeg 0x51000 12, memmoveSeg 0x52000 31,
  memclrSeg 0x53000 7]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x50000 ∧ ∃ d sr, args = [d, sr, 12]) ∨ (a = 0x51000 ∧ ∃ d, args = [d, 12]) ∨
  (a = 0x52000 ∧ ∃ d sr, args = [d, sr, 31]) ∨ (a = 0x53000 ∧ ∃ d, args = [d, 7])

def R : RtInv := toyR [] ok

theorem hmv12 : ∀ args, ok 0x50000 args → ∃ d sr, args = [d, sr, 12] := by
  intro args h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hcl12 : ∀ args, ok 0x51000 args → ∃ d, args = [d, 12] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hmv31 : ∀ args, ok 0x52000 args → ∃ d sr, args = [d, sr, 31] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hcl7 : ∀ args, ok 0x53000 args → ∃ d, args = [d, 7] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | (exfalso; omega)

theorem mv12 : MemmoveLive linked 0x50000 4096 R := by janus_live_memmove 12 hmv12
theorem cl12 : MemclrNoHeapPointersLive linked 0x51000 4096 R := by janus_live_memclr 12 hcl12
theorem mv31 : MemmoveLive linked 0x52000 4096 R := by janus_live_memmove 31 hmv31
theorem cl7 : MemclrNoHeapPointersLive linked 0x53000 4096 R := by janus_live_memclr 7 hcl7

end JanusTests.LiveStubSlice.Arm

namespace JanusTests.LiveStubSlice.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }

def linked : Janus.Amd64.Program := P.link [memmoveSeg 0x450000 12, memclrSeg 0x451000 12,
  memmoveSeg 0x452000 31, memclrSeg 0x453000 7]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x450000 ∧ ∃ d sr, args = [d, sr, 12]) ∨ (a = 0x451000 ∧ ∃ d, args = [d, 12]) ∨
  (a = 0x452000 ∧ ∃ d sr, args = [d, sr, 31]) ∨ (a = 0x453000 ∧ ∃ d, args = [d, 7])

def R : RtInv := toyR [] ok

theorem hmv12 : ∀ args, ok 0x450000 args → ∃ d sr, args = [d, sr, 12] := by
  intro args h
  rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hcl12 : ∀ args, ok 0x451000 args → ∃ d, args = [d, 12] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hmv31 : ∀ args, ok 0x452000 args → ∃ d sr, args = [d, sr, 31] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> first | exact h | (exfalso; omega)

theorem hcl7 : ∀ args, ok 0x453000 args → ∃ d, args = [d, 7] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ <;> first | exact h | (exfalso; omega)

theorem mv12 : MemmoveLive64 linked 0x450000 4096 R := by janus64_live_memmove 12 hmv12
theorem cl12 : MemclrNoHeapPointersLive64 linked 0x451000 4096 R := by janus64_live_memclr 12 hcl12
theorem mv31 : MemmoveLive64 linked 0x452000 4096 R := by janus64_live_memmove 31 hmv31
theorem cl7 : MemclrNoHeapPointersLive64 linked 0x453000 4096 R := by janus64_live_memclr 7 hcl7

end JanusTests.LiveStubSlice.Amd
