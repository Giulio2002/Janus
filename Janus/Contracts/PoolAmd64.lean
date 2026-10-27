import Janus.Contracts.Pool
import Janus.Contracts.MapAmd64
import Janus.Contracts.LiveAmd64

/-!
# Contracts of `sync.Pool` for one goroutine (amd64)

The amd64 counterparts of `Janus.Contracts.Pool` (see that file and docs/RUNTIME-CONTRACTS.md,
"sync.Pool"): the same functions with the same results (nil, or an object of shape `Sh` that
becomes caller-owned; `Put` gives it back), stated with the amd64 ABIInternal.
`sync.(*Pool).Get()` takes the pool in `RAX` (`regs 0`) and returns the interface in
`RAX`/`RBX` (`regs 0`, `regs 3`); `sync.(*Pool).Put(x)` takes the pool in `RAX` and `x` in
`RBX`/`RCX` (`regs 3`, `regs 1`). `CALL` pushes the return address, so the callee starts with
`[RSP]` holding it and returns to it with `RSP + 8`; `RBP`, `R14` (`g`) and `X15` (zero) are
preserved, every other general register, `X0`–`X14`, the upper `YMM` halves and the flags are
arbitrary afterwards (and so is any further vector state the model gains: the AVX-512 rule of
the integration branch leaves `zmmHi` and the mask registers unspecified after every call). A
call may write `rt` and its stack window: at most `stack` bytes below `RSP` (never the
return-address slot) and the argument spill slots `[RSP + 8, RSP + 8·(1 + nargs))`.

As in `Janus.Contracts.Pool`, `StackRoom64`, `LiveAt`, `LiveFrame`, `RtInv` and `view` come from
`Janus.Contracts.LiveAmd64`; the live set and the pooled object are kept apart from the window
`liveWin64` (the callee's stack and the return-address slot).
-/

namespace Janus.Contracts.PoolAmd64

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map
  Janus.Spec.Pool Janus.Contracts.Pool

/-- The return of a live pool call from `s` to `s'` (amd64): to the return address with `RSP + 8`
and `RBP`, `R14`, `X15` kept (`MapAmd64.keepABI`, `keepX15`), memory changed only in `rt` and
the callee's window, none of the live objects of `L` changed, and `P r m`. -/
def LiveRet (R : RtInv) (stack nargs : Nat) (L : List (Nat × Nat)) (s s' : State)
    (P : (Nat → W64) → Janus.Arm64.Memory → Prop) : Prop :=
  ∃ (r : Nat → W64) (x y : Nat → BitVec 128) (fl : Flags) (m : Janus.Arm64.Memory)
    (zh : Nat → BitVec 256) (kr : Nat → W64),
    s' = { s with regs := MapAmd64.keepABI s.regs r, xmm := MapAmd64.keepX15 s.xmm x,
                  ymmHi := y, flags := fl, mem := m, rip := retAddrOf s, zmmHi := zh, kreg := kr } ∧
    MemFrame s.mem m (R.rt ++ calleeStack64 s stack nargs) ∧ LiveFrame s.mem m L [] ∧ P r m

attribute [janus64_exec, janus64_post] LiveRet

/-- **`sync.(*Pool).Get()`** (amd64; `RAX = p`, a pool whose `New` is nil; result `RAX`/`RBX`),
as `Pool.PoolGetLive`. -/
def PoolGetLive (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat)
    (R : RtInv) (T : Nat) (Sh : PoolShape) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat), Summary p addr
    (fun s => CallOK64 s stack 1 ∧ StackRoom64 s stack 1 ∧
      s.mem.readLE ((s.regs 0).toNat + newOffset) 8 = 0 ∧
      LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s stack 1))
    (fun s s' => LiveRet R stack 1 L s s' fun r m =>
      NewSame (s.regs 0).toNat s.mem m ∧
      (((r 0).toNat = 0 ∧ (r 3).toNat = 0 ∧ R.inv b L (s.regs 14).toNat (view R.rt L m)) ∨
       ∃ rs, (r 0).toNat = T ∧ Sh m (r 3).toNat rs ∧ FreshFrom rs L ∧
         (∀ x ∈ rs, InRanges x.1 (x.2 - x.1) R.rt) ∧ LiveSep rs (liveWin64 s stack 1) ∧
         R.inv b (L ++ rs) (s.regs 14).toNat (view R.rt (L ++ rs) m)))

/-- **`sync.(*Pool).Put(x)`** (amd64; `RAX = p`, `RBX`/`RCX` the type and data words of `x`), as
`Pool.PoolPutLive`. -/
def PoolPutLive (p : Janus.Amd64.Program) (addr : Nat) (stack : Nat)
    (R : RtInv) (T : Nat) (Sh : PoolShape) : Prop :=
  ∀ (L : List (Nat × Nat)) (b : Nat) (rs : List (Nat × Nat)), Summary p addr
    (fun s => CallOK64 s stack 3 ∧ StackRoom64 s stack 3 ∧ (s.regs 3).toNat = T ∧
      Sh s.mem (s.regs 1).toNat rs ∧ (∀ r ∈ rs, r ∈ L) ∧
      LiveAt R addr [(s.regs 0).toNat] L b 0 (s.regs 14).toNat s.mem (liveWin64 s stack 3))
    (fun s s' => LiveRet R stack 3 L s s' fun _ m =>
      NewSame (s.regs 0).toNat s.mem m ∧
      R.inv b (dropAll L rs) (s.regs 14).toNat (view R.rt (dropAll L rs) m))

end Janus.Contracts.PoolAmd64
