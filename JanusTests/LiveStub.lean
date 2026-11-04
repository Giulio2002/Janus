import Janus

/-! The live runtime contracts hold for stub code placed at a program's own contract addresses
(`Janus.Contracts.LiveStub`, `LiveStubAmd64`): addresses other than the toy's `A0`, three
barriers 16 bytes apart (arm64), the allocation contracts, on both ISAs. -/

namespace JanusTests.LiveStub.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program :=
  { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0,
    contracts := [("runtime.newobject", 0x2a2a0), ("runtime.makeslice", 0x30000),
      ("runtime.mallocgc", 0x31000), ("runtime.gcWriteBarrier1", 0x8a430),
      ("runtime.gcWriteBarrier2", 0x8a440)] }

def linked : Program := P.link (stubSegs P)

def R : RtInv := toyR [] fun _ _ => True

theorem new_ : NewobjectLiveContract linked 0x2a2a0 4096 R := by janus_live_newobject
theorem make_ : MakesliceLiveContract linked 0x30000 4096 R := by janus_live_makeslice
theorem malloc_ : MallocgcLiveContract linked 0x31000 4096 R := by janus_live_mallocgc
theorem wb1 : WbLiveContract linked 0x8a430 4096 R 1 := by janus_live_wb 1
theorem wb2 : WbLiveContract linked 0x8a440 4096 R 2 := by janus_live_wb 2

end JanusTests.LiveStub.Arm

namespace JanusTests.LiveStub.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program :=
  { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0,
    contracts := [("runtime.newobject", 0x41d9c0), ("runtime.makeslice", 0x420000),
      ("runtime.mallocgc", 0x421000), ("runtime.gcWriteBarrier1", 0x47f680),
      ("runtime.gcWriteBarrier2", 0x47f6a0)] }

def linked : Janus.Amd64.Program := P.link (stubSegs P)

def R : RtInv := toyR [] fun _ _ => True

theorem new_ : NewobjectLiveContract64 linked 0x41d9c0 4096 R := by janus64_live_newobject
theorem make_ : MakesliceLiveContract64 linked 0x420000 4096 R := by janus64_live_makeslice
theorem malloc_ : MallocgcLiveContract64 linked 0x421000 4096 R := by janus64_live_mallocgc
theorem wb1 : WbLiveContract64 linked 0x47f680 4096 R 1 := by janus64_live_wb 1
theorem wb2 : WbLiveContract64 linked 0x47f6a0 4096 R 2 := by janus64_live_wb 2

end JanusTests.LiveStub.Amd
