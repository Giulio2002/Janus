import Janus

/-! The non-live allocation contracts at a program's own addresses, over a consumer-chosen `rt`
(`Janus.Contracts.StubAlloc`, `StubAllocAmd64`). -/

namespace JanusTests.StubAlloc.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.StubAlloc

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

/-- A heap at `0x40000` and two type descriptors the consumer owns. -/
def rt : List (Nat × Nat) := [(0x40000, 0x50000), (0x30000, 0x30010), (0x30100, 0x30110)]

def linked : Program := P.link [heapSeg 0x2a2a0 0x40000, heapSeg 0x2b000 0x40000, heapSeg 0x2c000 0x40000]

theorem new_ : NewobjectContract linked 0x2a2a0 rt 4096 (NewReadyAt rt 0x40000) := by
  janus_newobject 0x40000 (by simp [rt])

theorem malloc_ : MallocgcContract linked 0x2b000 rt 4096 (MallocReadyAt 0x40000) := by
  janus_mallocgc 0x40000 (by simp [rt])

theorem make_ : MakesliceContract linked 0x2c000 rt 4096 (MakeReadyAt rt 0x40000) := by
  janus_makeslice 0x40000 (by simp [rt])

end JanusTests.StubAlloc.Arm

namespace JanusTests.StubAlloc.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.StubAlloc Janus.Contracts.StubAllocAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }

def rt : List (Nat × Nat) := [(0x40000, 0x50000), (0x30000, 0x30010), (0x30100, 0x30110)]

def linked : Janus.Amd64.Program :=
  P.link [heapSeg 0x41d9c0 0x40000, heapSeg 0x41e000 0x40000, heapSeg 0x41f000 0x40000]

theorem new_ : NewobjectContract64 linked 0x41d9c0 rt 4096 (NewReadyAt rt 0x40000) := by
  janus64_newobject 0x40000 (by simp [rt])

theorem malloc_ : MallocgcContract64 linked 0x41e000 rt 4096 (MallocReadyAt 0x40000) := by
  janus64_mallocgc 0x40000 (by simp [rt])

theorem make_ : MakesliceContract64 linked 0x41f000 rt 4096 (MakeReadyAt rt 0x40000) := by
  janus64_makeslice 0x40000 (by simp [rt])

end JanusTests.StubAlloc.Amd
