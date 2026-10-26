import Janus.Contracts.Live
import Janus.Contracts.LiveCost
import Janus.Contracts.AllocAmd64
import Janus.Contracts.MallocSCAmd64
import Janus.Contracts.MemAmd64
import Janus.Contracts.Rt

/-!
# Live allocation contracts (amd64)

The amd64 counterpart of `Janus.Contracts.Live`, with the **same shape**: one runtime hypothesis
`R : RtInv` (`inv`, `ok`, `rt`, `ext`) threaded through every call, `∀ L b, Summary …` contracts
whose precondition is `LiveAt` (the same definition) and whose postcondition keeps the memory
frame (`MemFrame` in `R.rt ∪ window ∪ writes`, `LiveFrame` for `L`) and re-establishes `R.inv`.
The differences are the calling convention only: arguments `RAX, RBX, RCX, RDI, RSI`, the goroutine
`R14`, the stack window `calleeStack64`, and the canonical return state `retState64` (AVX-512
state `zmmHi`/`kreg` unspecified, `X15`, `FS`, the direction flag kept); the write barrier returns
in `wbRetX64` (`R11` = the buffer). Contracts are named like the arm64 ones with a `64` suffix.
-/

namespace Janus.Contracts

open Janus Janus.Amd64 Janus.Amd64.Tactic Janus.Spec

/-- The runtime's stack check falls through (amd64): `g.stackguard0 + stack < RSP`, its word
outside the callee's window. -/
@[reducible] def StackRoom64 (s : State) (stack nargs : Nat) : Prop :=
  GuardOK64 s stack ∧ Outside ((s.regs 14).toNat + 16) 8 (calleeStack64 s stack nargs)

/-- The shape of a live allocation contract's postcondition (amd64): as `LiveAllocRet`, with
`retState64`. -/
@[reducible] def LiveAllocRet64 (R : RtInv) (stack nargs : Nat) (res : W64 → List W64)
    (L : List (Nat × Nat)) (b cost round : Nat) (s s' : State) (Q : Memory → Nat → Prop) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk (res ptr) f x yh m zh kr ∧
      MemFrame s.mem m (R.rt ++ calleeStack64 s stack nargs) ∧ LiveFrame s.mem m L [] ∧
      Q m ptr.toNat ∧ ApartAll ptr.toNat round (calleeStack64 s stack nargs) ∧
      R.inv (b - cost) (L ++ [(ptr.toNat, ptr.toNat + round)]) (s.regs 14).toNat
        (view R.rt (L ++ [(ptr.toNat, ptr.toNat + round)]) m)

@[reducible] def mallocgcRound64 (s : State) : Nat :=
  blockSize (s.regs 0).toNat ((s.regs 3).toNat == 0 || typNoscan s.mem (s.regs 3).toNat)
@[reducible] def newobjectRound64 (s : State) : Nat :=
  blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)
@[reducible] def makesliceRound64 (s : State) : Nat :=
  blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat) (typNoscan s.mem (s.regs 0).toNat)
@[reducible] def growsliceRound64 (s : State) : Nat := 8 * growCap8 (s.regs 3).toNat (s.regs 1).toNat

attribute [janus64_exec, janus64_post] mallocgcRound64 newobjectRound64 makesliceRound64 growsliceRound64

/-- **`runtime.mallocgc(size, typ, needzero)`, live** (amd64). -/
def MallocgcLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MallocgcPre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (calleeStack64 s stack 3))
    (fun s s' => LiveAllocRet64 R stack 3 (fun ptr => [ptr]) L b (mallocgcRound64 s) (mallocgcRound64 s)
      s s' fun m ptr => 0 < (s.regs 0).toNat → mallocgcObj64 R.rt s m ptr ∧ ApartAll ptr (mallocgcRound64 s) L)

/-- **`runtime.newobject(typ)`, live** (amd64). -/
def NewobjectLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => NewobjectPre64 stack s ∧ StackRoom64 s stack 1 ∧
      LiveAt R addr [(s.regs 0).toNat] L b (newobjectRound64 s) (s.regs 14).toNat s.mem
        (calleeStack64 s stack 1))
    (fun s s' => LiveAllocRet64 R stack 1 (fun ptr => [ptr]) L b (newobjectRound64 s) (newobjectRound64 s)
      s s' fun m ptr => 0 < typSize s.mem (s.regs 0).toNat →
        newobjectObj64 R.rt s m ptr ∧ ApartAll ptr (newobjectRound64 s) L)

/-- **`runtime.makeslice(et, len, cap)`, live** (amd64). -/
def MakesliceLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MakeslicePre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (makesliceRound64 s)
        (s.regs 14).toNat s.mem (calleeStack64 s stack 3))
    (fun s s' => LiveAllocRet64 R stack 3 (fun ptr => [ptr]) L b (makesliceRound64 s) (makesliceRound64 s)
      s s' fun m ptr => 0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat →
        makesliceObj64 R.rt s m ptr ∧ ApartAll ptr (makesliceRound64 s) L)

/-- **`runtime.growslice`, live** (amd64; 8-byte pointer-free elements): as `GrowsliceLiveContract`
(the old array stays in `L`). -/
def GrowsliceLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => GrowslicePre64 stack s ∧ StackRoom64 s stack 5 ∧
      LiveAt R addr (growsliceArgs64 s) L b (growsliceRound64 s) (s.regs 14).toNat s.mem
        (calleeStack64 s stack 5))
    (fun s s' => LiveAllocRet64 R stack 5
      (fun ptr => [ptr, s.regs 3, BitVec.ofNat 64 (growCap8 (s.regs 3).toNat (s.regs 1).toNat)])
      L b (growsliceRound64 s) (growsliceRound64 s) s s' fun m ptr =>
        growsliceObj64 R.rt s m ptr ∧ ApartAll ptr (growsliceRound64 s) L)

/-- **`runtime.mallocgcSmallNoScanSC<n>`, live** (amd64). -/
def MallocgcSmallNoScanSCLiveContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (calleeStack64 s stack 3)) ∧
      NoScanArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => LiveAllocRet64 R stack 3 (fun ptr => [ptr]) L b (mallocgcRound64 s) (mallocgcRound64 s)
      s s' fun m ptr => mallocgcObj64 R.rt s m ptr ∧ ApartAll ptr (mallocgcRound64 s) L)

/-- **`runtime.mallocgcSmallScanNoHeaderSC<n>`, live** (amd64). -/
def MallocgcSmallScanNoHeaderSCLiveContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (calleeStack64 s stack 3)) ∧
      ScanArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => LiveAllocRet64 R stack 3 (fun ptr => [ptr]) L b (mallocgcRound64 s) (mallocgcRound64 s)
      s s' fun m ptr => mallocgcObj64 R.rt s m ptr ∧ ApartAll ptr (mallocgcRound64 s) L)

/-- **`runtime.mallocgcTinySize<n>`, live** (amd64). -/
def MallocgcTinySizeLiveContract64 (n : Nat) (p : Janus.Amd64.Program) (addr : Nat)
    (stack : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => (MallocgcPre64 stack s ∧ StackRoom64 s stack 3 ∧
      LiveAt R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b (mallocgcRound64 s)
        (s.regs 14).toNat s.mem (calleeStack64 s stack 3)) ∧
      TinyArgs n s.mem (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => LiveAllocRet64 R stack 3 (fun ptr => [ptr]) L b (mallocgcRound64 s) (mallocgcRound64 s)
      s s' fun m ptr => mallocgcObj64 R.rt s m ptr ∧ ApartAll ptr (mallocgcRound64 s) L)

theorem MallocgcLiveContract64.smallNoScanSC {n : Nat} {p : Janus.Amd64.Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MallocgcLiveContract64 p addr stack R) :
    MallocgcSmallNoScanSCLiveContract64 n p addr stack R := fun L b =>
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4 (by have := hp.2.1; omega), h5, h6⟩

theorem MallocgcLiveContract64.smallScanNoHeaderSC {n : Nat} {p : Janus.Amd64.Program} {addr : Nat}
    {stack : Nat} {R : RtInv} (h : MallocgcLiveContract64 p addr stack R) :
    MallocgcSmallScanNoHeaderSCLiveContract64 n p addr stack R := fun L b =>
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4 hp.2.1, h5, h6⟩

theorem MallocgcLiveContract64.tinySize {n : Nat} {p : Janus.Amd64.Program} {addr : Nat} {stack : Nat}
    {R : RtInv} (h : MallocgcLiveContract64 p addr stack R) :
    MallocgcTinySizeLiveContract64 n p addr stack R := fun L b =>
  Summary.mono (h L b) (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨ptr, j, f, x, yh, m, zh, kr, h1, h2, h3, h4 (by obtain ⟨h0, -, hs, -⟩ := hp.2; omega), h5, h6⟩

/-! ## The write barrier -/

/-- The state `gcWriteBarrierN` returns in (amd64): `RSP + 8`, `R11 = buf`, every other general
register, `X15`, `FS` and the direction flag kept, the flags, `X0`–`X14`, the upper halves and the
AVX-512 state unspecified. -/
def wbRetX64 (s : State) (buf : W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64) : State :=
  { s with regs := fun i => if i = 4 then s.regs 4 + 8#64 else if i = 11 then buf else s.regs i,
           rip := retAddrOf s, flags := f, xmm := fun i => if i = 15 then s.xmm 15 else x i,
           ymmHi := yh, mem := m, zmmHi := zh, kreg := kr }

attribute [janus64_exec, janus64_post] wbRetX64

/-- **`runtime.gcWriteBarrierN`, live** (amd64, `N = n`): as `WbLiveContract`. -/
def WbLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv) (n : Nat) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK64 s stack 0 ∧ R.ok addr [n] ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
      LiveSep L [((s.regs 4).toNat - stack, (s.regs 4).toNat)] ∧
      LiveSep [((s.regs 4).toNat - stack, (s.regs 4).toNat)] R.rt)
    (fun s s' => ∃ (buf : W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
        (zh : Nat → BitVec 256) (kr : Nat → W64),
      s' = wbRetX64 s buf f x yh m zh kr ∧
      MemFrame s.mem m (R.rt ++ [((s.regs 4).toNat - stack, (s.regs 4).toNat)]) ∧ LiveFrame s.mem m L [] ∧
      WbSlots R.rt m buf.toNat n ∧ ApartAll buf.toNat (8 * n) L ∧
      ApartAll buf.toNat (8 * n) [((s.regs 4).toNat - stack, (s.regs 4).toNat)] ∧
      InvSlots R b L (s.regs 14).toNat R.rt m buf.toNat n)

/-! ## The string, slice and bulk-barrier specs -/

/-- The precondition of `RtLiveContract64`. -/
@[reducible] def RtLivePre64 (stack : Nat) (R : RtInv) (sp : RtSpec) (ls : LiveSpec)
    (addr : Nat) (L : List (Nat × Nat)) (b : Nat) (s : State) : Prop :=
  CallOK64 s stack sp.nargs ∧ sp.pre (argWords64 s sp.nargs) s.mem ∧
    ReadsOutside (sp.reads (argWords64 s sp.nargs) s.mem) (calleeStack64 s stack sp.nargs) ∧
    (match sp.guard with
      | some adj => GuardOK64 s adj ∧ Outside ((s.regs 14).toNat + 16) 8 (calleeStack64 s stack sp.nargs)
      | none => True) ∧
    StackRoom64 s stack sp.nargs ∧
    LiveAt R addr (argWords64 s sp.nargs) L b (ls.cost (argWords64 s sp.nargs) s.mem) (s.regs 14).toNat
      s.mem (calleeStack64 s stack sp.nargs)

/-- The postcondition of `RtLiveContract64`. -/
@[reducible] def RtLivePost64 (stack : Nat) (R : RtInv) (sp : RtSpec) (ls : LiveSpec)
    (L : List (Nat × Nat)) (b : Nat) (s s' : State) : Prop :=
  ∃ (r0 r1 r2 : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = retState64 s junk [r0, r1, r2] f x yh m zh kr ∧
      MemFrame s.mem m (rtIf sp.rtWrites R.rt ++ calleeStack64 s stack sp.nargs ++
        sp.writes (argWords64 s sp.nargs) s.mem) ∧
      sp.post R.rt (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat m ∧
      LiveFrame s.mem m L (sp.writes (argWords64 s sp.nargs) s.mem) ∧
      FreshFrom (ls.fresh (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) L ∧
      LiveApart (liveAdds ls (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat)
        (calleeStack64 s stack sp.nargs) ∧
      R.inv (b - ls.cost (argWords64 s sp.nargs) s.mem)
        (L ++ liveAdds ls (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) (s.regs 14).toNat
        (view R.rt (L ++ liveAdds ls (argWords64 s sp.nargs) s.mem r0.toNat r1.toNat r2.toNat) m)

/-- **The live amd64 contract of the spec `sp`** (with the live data `ls`) at `addr`. -/
def RtLiveContract64 (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat) (R : RtInv)
    (sp : RtSpec) (ls : LiveSpec) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr (RtLivePre64 stack R sp ls addr L b)
    (RtLivePost64 stack R sp ls L b)

/-! ## Memory copies and clears (amd64)

As arm64 `MemmoveLive` etc.: `RAX = dst`, `RBX = src`, `RCX = n` (`memmove`); the destination is a
live object or outside `R.rt`, and also outside the return-address slot. -/

/-- The destination of a copy or clear (amd64). -/
def LiveDest64 (R : RtInv) (L : List (Nat × Nat)) (s : State) (d nargs a n : Nat) : Prop :=
  a + n ≤ 2 ^ 48 ∧ s.mem.accessible a n true = true ∧ Outside a n (calleeStack64 s d nargs) ∧
    (InRanges a n L ∨ Outside a n R.rt) ∧ Outside a n [((s.regs 4).toNat, (s.regs 4).toNat + 8)]

/-- The return of a live copy or clear (amd64): `retState64` without result registers. -/
def LiveMemRet64 (R : RtInv) (d nargs : Nat) (extra L : List (Nat × Nat)) (b : Nat) (s s' : State)
    (P : Memory → Prop) : Prop :=
  ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64), s' = retState64 s junk [] f x yh m zh kr ∧
    MemFrame s.mem m (R.rt ++ calleeStack64 s d nargs ++ extra) ∧ LiveFrame s.mem m L extra ∧
    R.inv b L (s.regs 14).toNat (view R.rt L m) ∧ P m

@[reducible] def LiveMemAt64 (R : RtInv) (addr : Nat) (args : List Nat) (L : List (Nat × Nat)) (b : Nat)
    (s : State) (win : List (Nat × Nat)) : Prop :=
  R.ok addr args ∧ R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧ LiveSep L win ∧ LiveSep win R.rt

/-- The ABI part of a copy's precondition (amd64): `MemAmd64.EqPre`. -/
@[reducible] def MemPre64 (d nargs : Nat) (s : State) : Prop := MemAmd64.EqPre d nargs s

/-- **`runtime.memmove(dst, src, n)`, live** (amd64). -/
def MemmoveLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MemPre64 d 3 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (calleeStack64 s d 3) ∧
      MemAmd64.Input s d 3 (s.regs 3).toNat (s.regs 1).toNat ∧
      LiveDest64 R L s d 3 (s.regs 0).toNat (s.regs 1).toNat)
    (fun s s' => LiveMemRet64 R d 3 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 1).toNat)] L b s s'
      fun m => Mem.Copied s.mem m (s.regs 0).toNat (s.regs 3).toNat (s.regs 1).toNat)

/-- **`runtime.memclrNoHeapPointers(ptr, n)`, live** (amd64). -/
def MemclrNoHeapPointersLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MemPre64 d 2 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat] L b s (calleeStack64 s d 2) ∧
      LiveDest64 R L s d 2 (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => LiveMemRet64 R d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 3).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 3).toNat)

/-- **`runtime.typedmemmove(typ, dst, src)`, live** (amd64; `RAX = typ`, `RBX = dst`, `RCX = src`). -/
def TypedMemmoveLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MemPre64 d 3 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] L b s (calleeStack64 s d 3) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack64 s d 3) ∧
      MemAmd64.Input s d 3 (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat) ∧
      LiveDest64 R L s d 3 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => LiveMemRet64 R d 3
      [((s.regs 3).toNat, (s.regs 3).toNat + typSize s.mem (s.regs 0).toNat)] L b s s'
      fun m => Mem.Copied s.mem m (s.regs 3).toNat (s.regs 1).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.typedmemclr(typ, ptr)`, live** (amd64). -/
def TypedMemclrLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MemPre64 d 2 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat] L b s (calleeStack64 s d 2) ∧
      TypeOK s.mem (s.regs 0).toNat ∧ Outside (s.regs 0).toNat 16 (calleeStack64 s d 2) ∧
      LiveDest64 R L s d 2 (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))
    (fun s s' => LiveMemRet64 R d 2
      [((s.regs 3).toNat, (s.regs 3).toNat + typSize s.mem (s.regs 0).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 3).toNat (typSize s.mem (s.regs 0).toNat))

/-- **`runtime.memclrHasPointers(ptr, n)`, live** (amd64). -/
def MemclrHasPointersLive64 (p : Janus.Amd64.Program) (addr : Nat) (d : Nat) (R : RtInv) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => MemPre64 d 2 s ∧
      LiveMemAt64 R addr [(s.regs 0).toNat, (s.regs 3).toNat] L b s (calleeStack64 s d 2) ∧
      (s.regs 0).toNat % 8 = 0 ∧ (s.regs 3).toNat % 8 = 0 ∧
      LiveDest64 R L s d 2 (s.regs 0).toNat (s.regs 3).toNat)
    (fun s s' => LiveMemRet64 R d 2 [((s.regs 0).toNat, (s.regs 0).toNat + (s.regs 3).toNat)] L b s s'
      fun m => Mem.Zeroed m (s.regs 0).toNat (s.regs 3).toNat)

/-- A state is `retState64` of the call state when it returns to the return address with
`RSP + 8`, `RBP`, `R14`, `X15`, the direction flag, `FS` and `MXCSR` kept and the result
registers `RAX, RBX, RCX` as `res` (a result register past `res`'s length is unconstrained). The
converse of the definition, for proofs that run a callee's code. -/
theorem retState64_intro {s s' : State} {res : List W64} (hrip : s'.rip = retAddrOf s)
    (h4 : s'.regs 4 = s.regs 4 + 8#64) (h5 : s'.regs 5 = s.regs 5) (h14 : s'.regs 14 = s.regs 14)
    (hx : s'.xmm 15 = s.xmm 15) (hfs : s'.fsBase = s.fsBase) (hdf : s'.df = s.df)
    (hmx : s'.mxcsr = s.mxcsr)
    (h0 : s'.regs 0 = res.getD 0 (s'.regs 0)) (h1 : s'.regs 3 = res.getD 1 (s'.regs 3))
    (h2 : s'.regs 1 = res.getD 2 (s'.regs 1))
    (hx87 : s'.x87 = s.x87 := by first | rfl | simp_all)
    (hfw : s'.fpucw = s.fpucw := by first | rfl | simp_all) :
    ∃ (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64), s' = retState64 s junk res f x yh m zh kr := by
  refine ⟨s'.regs, s'.flags, s'.xmm, s'.ymmHi, s'.mem, s'.zmmHi, s'.kreg, ?_⟩
  obtain ⟨r, rip, fl, xm, mem, yh, fs, df, mx, x8, fw⟩ := s'
  simp only at hrip h4 h5 h14 hx hfs hdf hmx hx87 hfw h0 h1 h2 ⊢
  subst hrip hfs hdf hmx hx87 hfw
  simp only [retState64, State.mk.injEq, and_true, true_and]
  constructor
  · funext i
    simp only [callRegs64]
    split
    · rename_i hi; subst hi; exact h4
    · split
      · rename_i hi; rcases hi with rfl | rfl <;> simp [h5, h14]
      · split
        · rename_i hi; subst hi; exact h0
        · split
          · rename_i hi; subst hi; exact h1
          · split
            · rename_i hi; subst hi; exact h2
            · rfl
  · funext i
    split
    · rename_i hi; subst hi; exact hx
    · rfl

end Janus.Contracts
