import Janus
import Janus.Contracts.LiveStubMemmoveUpto
import Janus.Contracts.LiveStubMemmoveUptoAmd64

/-! `memmove(dst, src, 0)` (both ISAs): `MemmoveZeroLive` holds of the pinned runtime code and of the variable-size stub
at a program's own address, for every runtime hypothesis; a stub that writes when `n = 0` is refused; and
`MemmoveLive.withZero` accepts a call with `n = 0` and a destination nothing is known about. -/

namespace JanusTests.MemmoveZero.Arm

open Janus Janus.Arm64 Janus.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }

-- the pinned go1.26 runtime.memmove, at another address than `LiveSat`'s `A0`
def linkedPinned : Program := P.link [⟨"runtime.memmove", 0x70000, LiveSat.memmovePinned⟩]
theorem pinned0 (d : Nat) (R : RtInv) : MemmoveZeroLive linkedPinned 0x70000 d R := by
  janus_live_memmove_zero

-- the variable-size stub: its compare chain falls through to `RET`
def linkedUpto : Program := P.link [memmoveUptoSeg 0x70000 8]
theorem upto0 (d : Nat) (R : RtInv) : MemmoveZeroLive linkedUpto 0x70000 d R := by
  janus_live_memmove_zero

-- red team: the fixed-size stub copies 8 bytes whatever `n` is, so it writes memory the contract keeps
def linked8 : Program := P.link [memmoveSeg 0x70000 8]
theorem rt_writes : True := by
  fail_if_success
    have : MemmoveZeroLive linked8 0x70000 4096 (toyR [] fun _ _ => True) := by
      janus_live_memmove_zero
  trivial

-- `withZero`: a call with `n = 0` needs no fact about `dst` or `src`
example {p : Program} {addr d : Nat} {R : RtInv} (h : MemmoveLive p addr d R) (hz : MemmoveZeroLive p addr d R)
    (L : List (Nat × Nat)) (b : Nat) (s : State) (hpc : s.pc = BitVec.ofNat 64 addr) (hE : Mem.EqPre d 3 s)
    (hA : LiveMemAt R addr [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] L b s (calleeStack s d 3))
    (h2 : (s.regs 2).toNat = 0) :
    ReachesRet p (s.regs 30) s fun s' =>
      LiveMemRet R d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 2).toNat)] L b s s'
        fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat :=
  MemmoveLive.withZero h hz L b s hpc ⟨hE, hA, Or.inl h2⟩

end JanusTests.MemmoveZero.Arm

namespace JanusTests.MemmoveZero.Amd

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }

def linkedPinned : Janus.Amd64.Program := P.link [⟨"runtime.memmove", 0x470000, LiveSatAmd64.memmovePinned64⟩]
theorem pinned0 (d : Nat) (R : RtInv) : MemmoveZeroLive64 linkedPinned 0x470000 d R := by
  janus64_live_memmove_zero

def linkedUpto : Janus.Amd64.Program := P.link [memmoveUptoSeg64 0x470000 8]
theorem upto0 (d : Nat) (R : RtInv) : MemmoveZeroLive64 linkedUpto 0x470000 d R := by
  janus64_live_memmove_zero

-- red team: the fixed-size stub writes 8 bytes whatever `n` is
def linked8 : Janus.Amd64.Program := P.link [memmoveSeg 0x470000 8]
theorem rt_writes : True := by
  fail_if_success
    have : MemmoveZeroLive64 linked8 0x470000 4096 (toyR [] fun _ _ => True) := by
      janus64_live_memmove_zero
  trivial

example {p : Janus.Amd64.Program} {addr d : Nat} {R : RtInv} (h : MemmoveLive64 p addr d R)
    (hz : MemmoveZeroLive64 p addr d R) (L : List (Nat × Nat)) (b : Nat) (s : State)
    (hpc : s.rip = BitVec.ofNat 64 addr) (hE : MemPre64 d 3 s)
    (hA : LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (liveWin64 s d 3))
    (h1 : (s.regs 1).toNat = 0) :
    ReachesRet p (retAddrOf s) s fun s' =>
      LiveMemRet64 R d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] L b s s'
        fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat :=
  MemmoveLive64.withZero h hz L b s hpc ⟨hE, hA, Or.inl h1⟩

end JanusTests.MemmoveZero.Amd
