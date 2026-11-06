import Janus
import Janus.Contracts.LiveStubGrow
import Janus.Contracts.LiveStubGrowAmd64

/-! U-GROWMULTI: `growslice` with an old array of several copy chunks (16, 32 and 40 old bytes,
2 / 4 / 5 chunks of `chunkList`). The macros put `p + ob ≤ 2^48` (the first component of
`Readable m p ob` in `growsliceSpec.pre`) into the context before the stepper runs, so the address
of every later chunk is known not to wrap. Size 1 (`[]byte`).

Red team: the extra fact is derived from `pre` (`growslice_bound`), never assumed, so a stub that
copies the wrong number of bytes, or a contract with the wrong capacity, still has no proof. -/

namespace JanusTests.LiveStubGrowMulti.Arm

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStub

def P : Program := { segments := [⟨"f", 0x1000, [0xd65f03c0]⟩], stubs := [], exitAddr := 0 }
def tys : Tys := [(0x30000, 1, 0)]

-- growslice(p, n, c0, num, uint8): 24/16/8 -> 16 old bytes, cap 32; 40/32/8 -> 32 old bytes, cap 64;
-- 48/40/8 -> 40 old bytes, cap 80
def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x61000 ∧ ∃ p, args = [p, 24, 16, 8, 0x30000]) ∨
  (a = 0x62000 ∧ ∃ p, args = [p, 40, 32, 8, 0x30000]) ∨
  (a = 0x63000 ∧ ∃ p, args = [p, 48, 40, 8, 0x30000])

def R : RtInv := toyR tys ok

def linked : Program := P.link [growsliceSeg 0x61000 16 32 32, growsliceSeg 0x62000 32 64 64,
  growsliceSeg 0x63000 40 80 80]

theorem hok16 : ∀ args, ok 0x61000 args → ∃ p, args = [p, 24, 16, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  · exfalso; omega
  · exfalso; omega

theorem hok32 : ∀ args, ok 0x62000 args → ∃ p, args = [p, 40, 32, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩ | ⟨h, _⟩
  · exfalso; omega
  · exact ⟨p, h⟩
  · exfalso; omega

theorem hok40 : ∀ args, ok 0x63000 args → ∃ p, args = [p, 48, 40, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, p, h⟩
  · exfalso; omega
  · exfalso; omega
  · exact ⟨p, h⟩

set_option maxHeartbeats 4000000 in
theorem g16 : RtLiveContract linked 0x61000 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 24 16 8 32 32 hok16

-- the consumer case (FV-C, `MarshalSSZAppend` growth path): 32 old bytes.
set_option maxHeartbeats 4000000 in
theorem g32 : RtLiveContract linked 0x62000 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 40 32 8 64 64 hok32

set_option maxHeartbeats 4000000 in
theorem g40 : RtLiveContract linked 0x63000 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (0x30000, 1, 0) 48 40 8 80 80 hok40

/-! Red team. -/

/-- a wrong capacity (32 where the request gives 64) is not provable. -/
theorem rt_wrongcap : True := by
  fail_if_success
    have : RtLiveContract linked 0x62000 4096 R growsliceSpec growsliceLive := by
      janus_live_growslice (0x30000, 1, 0) 40 32 8 64 32 hok32
  trivial

/-- a stub that copies 16 bytes where the request has 32 old bytes is not provable. -/
def linkedShort : Program := P.link [growsliceSeg 0x62000 16 64 64]

set_option maxHeartbeats 4000000 in
theorem rt_shortcopy : True := by
  fail_if_success
    have : RtLiveContract linkedShort 0x62000 4096 R growsliceSpec growsliceLive := by
      janus_live_growslice (0x30000, 1, 0) 40 32 8 64 64 hok32
  trivial

/-- the extra fact is a consequence of `pre`: an old array that wraps `2^48` makes `pre` false. -/
theorem rt_bound_is_derived {tys : Tys} {ok : Nat → List Nat → Prop} {addr : Nat} {n c0 num ob oldp : Nat}
    {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hq0 : (s.regs 0).toNat = oldp)
    (hargs : argWords s growsliceSpec.nargs = [oldp, n, c0, num, 0x30000])
    (hsz : typSize s.mem 0x30000 = 1) (hob : (n - num) * 1 = ob)
    (hwrap : 2 ^ 48 < (s.regs 0).toNat + ob) : False :=
  absurd (growslice_bound (t := (0x30000, 1, 0)) pre hq0 hargs hsz hob) (Nat.not_le.mpr hwrap)

end JanusTests.LiveStubGrowMulti.Arm

namespace JanusTests.LiveStubGrowMulti.Amd

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def P : Janus.Amd64.Program := { segments := [⟨"f", 0x401000, [0xc3]⟩], stubs := [], exitAddr := 0 }
def tys : Tys := [(0x30000, 1, 0)]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = 0x461000 ∧ ∃ p, args = [p, 24, 16, 8, 0x30000]) ∨
  (a = 0x462000 ∧ ∃ p, args = [p, 40, 32, 8, 0x30000]) ∨
  (a = 0x463000 ∧ ∃ p, args = [p, 48, 40, 8, 0x30000])

def R : RtInv := toyR tys ok

def linked : Janus.Amd64.Program := P.link [growsliceSeg 0x461000 16 32 32, growsliceSeg 0x462000 32 64 64,
  growsliceSeg 0x463000 40 80 80]

theorem hok16 : ∀ args, ok 0x461000 args → ∃ p, args = [p, 24, 16, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨_, p, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨p, h⟩
  · exfalso; omega
  · exfalso; omega

theorem hok32 : ∀ args, ok 0x462000 args → ∃ p, args = [p, 40, 32, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨_, p, h⟩ | ⟨h, _⟩
  · exfalso; omega
  · exact ⟨p, h⟩
  · exfalso; omega

theorem hok40 : ∀ args, ok 0x463000 args → ∃ p, args = [p, 48, 40, 8, (0x30000, 1, 0).1] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, p, h⟩
  · exfalso; omega
  · exfalso; omega
  · exact ⟨p, h⟩

set_option maxHeartbeats 4000000 in
theorem g16 : RtLiveContract64 linked 0x461000 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (0x30000, 1, 0) 24 16 8 32 32 hok16

-- the consumer case (FV-C, `MarshalSSZAppend` growth path): 32 old bytes.
set_option maxHeartbeats 4000000 in
theorem g32 : RtLiveContract64 linked 0x462000 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (0x30000, 1, 0) 40 32 8 64 64 hok32

set_option maxHeartbeats 4000000 in
theorem g40 : RtLiveContract64 linked 0x463000 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (0x30000, 1, 0) 48 40 8 80 80 hok40

theorem rt_wrongcap : True := by
  fail_if_success
    have : RtLiveContract64 linked 0x462000 4096 R growsliceSpec growsliceLive := by
      janus64_live_growslice (0x30000, 1, 0) 40 32 8 64 32 hok32
  trivial

def linkedShort : Janus.Amd64.Program := P.link [growsliceSeg 0x462000 16 64 64]

set_option maxHeartbeats 4000000 in
theorem rt_shortcopy : True := by
  fail_if_success
    have : RtLiveContract64 linkedShort 0x462000 4096 R growsliceSpec growsliceLive := by
      janus64_live_growslice (0x30000, 1, 0) 40 32 8 64 64 hok32
  trivial

theorem rt_bound_is_derived {tys : Tys} {ok : Nat → List Nat → Prop} {addr : Nat} {n c0 num ob oldp : Nat}
    {L : List (Nat × Nat)} {b : Nat} {s : State}
    (pre : RtLivePre64 4096 (toyR tys ok) growsliceSpec growsliceLive addr L b s)
    (hq0 : (s.regs 0).toNat = oldp)
    (hargs : argWords64 s growsliceSpec.nargs = [oldp, n, c0, num, 0x30000])
    (hsz : typSize s.mem 0x30000 = 1) (hob : (n - num) * 1 = ob)
    (hwrap : 2 ^ 48 < (s.regs 0).toNat + ob) : False :=
  absurd (growslice_bound64 (t := (0x30000, 1, 0)) pre hq0 hargs hsz hob) (Nat.not_le.mpr hwrap)

end JanusTests.LiveStubGrowMulti.Amd
