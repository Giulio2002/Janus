import Janus.Contracts.Slice

/-!
# Runtime contracts: the GC write barrier (arm64 and amd64)

With the garbage collector marking, Go's compiler guards every store of a pointer into the heap
(and every bulk copy or clear of pointerful memory) with the global flag
`runtime.writeBarrier.enabled`:

```go
if writeBarrier.enabled {
	buf := gcWriteBarrierN()   // N = 1 … 8: room for N pointers in the P's write-barrier buffer
	buf[0] = new; buf[1] = old // … then the store itself
}
*slot = new
```

and, for a whole typed value, `if writeBarrier.enabled { wbMove(typ, dst, src) }` before the
`memmove` (`wbZero(typ, dst)` before a clear). This file states what those functions do:

* **`gcWriteBarrierN`** (`runtime/asm_arm64.s`, `asm_amd64.s`; not a Go ABIInternal call: it
  preserves almost every register): reserves `8·N` bytes in the P's buffer `p.wbBuf` and returns
  their address (arm64 `R25`, amd64 `R11`); when the buffer is full it first flushes it
  (`wbBufFlush`, which hands the pointers to the GC). Everything it writes is runtime memory
  (`rt`) or its own frame below `SP`. `WbContract`/`WbContract64` state it with the registers it
  may change: arm64 `R25` (the result), `R16`, `R17`, `R27`, the flags and the SIMD&FP registers
  (`wbBufFlush` is Go code; the assembly saves the other general registers around it, the
  compiler saves vector registers itself); amd64 `R11` (the result), the flags and `X0`–`X14`.
* **`wbZero(typ, dst)`, `wbMove(typ, dst, src)`** (`runtime/mbarrier.go`): only the bulk barrier
  (`bulkBarrierPreWrite`), which reads the pointer slots of `dst` (and `src`) and appends them to
  the buffer: they change runtime memory only, and do not zero or copy anything themselves.
* **The flag** is ordinary memory (the 32-bit word `runtime.writeBarrier` at an address the code
  loads with `ADRP`/RIP-relative addressing). A theorem states its value in its precondition or
  covers both values; the contracts above hold either way. `WriteBarrierOn m flag` names it.

`examples/proofs/WriteBarrier.lean` and `examples/proofs-amd64/WriteBarrier/Proof.lean` prove
from the binary's code that every `gcWriteBarrierN` (`N = 1 … 8`) meets its contract when the
buffer has room (the witness of round 9's rule: a contract must be satisfiable by the real
runtime).
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Spec

/-- The write barrier is on: the 32-bit flag word `runtime.writeBarrier.enabled` at `flag` is
non-zero. -/
def WriteBarrierOn (m : Memory) (flag : Nat) : Prop := m.readLE flag 4 ≠ 0

/-- **`runtime.wbZero(typ, dst)`**: the bulk barrier before clearing a value of type `typ` at
`dst`; runtime memory only. Words: `typ, dst`. -/
def wbZeroSpec : RtSpec where
  nargs := 2
  pre a m := TypeOK m (arg a 0) ∧ Readable m (arg a 1) (typSize m (arg a 0))
  post _ _ _ _ _ _ _ := True

/-- **`runtime.wbMove(typ, dst, src)`**: the bulk barrier before copying a value of type `typ`
from `src` to `dst`; runtime memory only. Words: `typ, dst, src`. -/
def wbMoveSpec : RtSpec where
  nargs := 3
  pre a m := TypeOK m (arg a 0) ∧ Readable m (arg a 1) (typSize m (arg a 0)) ∧
    Readable m (arg a 2) (typSize m (arg a 0))
  post _ _ _ _ _ _ _ := True

/-! ## `gcWriteBarrierN` (arm64) -/

/-- The general registers after `gcWriteBarrierN` (arm64): `R25 = buf`, `R16`, `R17`, `R27` from
`junk`, every other register unchanged. -/
def wbRegs (old junk : Nat → W64) (buf : W64) : Nat → W64 :=
  fun i => if i = 25 then buf else if i = 16 ∨ i = 17 ∨ i = 27 then junk i else old i

@[janus_exec, janus_post] theorem wbRegs_apply (old junk : Nat → W64) (buf : W64) (i : Nat) :
    wbRegs old junk buf i = if i = 25 then buf else if i = 16 ∨ i = 17 ∨ i = 27 then junk i else old i := rfl

/-- `8·n` bytes for the barrier to fill: inside `rt`, writable, 8-aligned. -/
def WbSlots (rt : List (Nat × Nat)) (m : Memory) (buf n : Nat) : Prop :=
  InRanges buf (8 * n) rt ∧ buf + 8 * n ≤ 2 ^ 48 ∧ m.accessible buf (8 * n) true = true ∧ buf % 8 = 0

/-- **`runtime.gcWriteBarrierN`** (arm64, `N = n`): from a call (`BL`, return address in `X30`,
`SP` 16-aligned, `[SP - stack, SP)` writable) at which the runtime is ready (`Ready H rt [n]`),
it returns to `X30` with `R25` = the address of `8·n` fresh buffer bytes (`WbSlots`),
registers as `wbRegs`, memory changed only in `rt` and `[SP - stack, SP - 8)`. -/
def WbContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat) (H : RtReady)
    (n : Nat) : Prop :=
  Tactic.Summary p addr (fun s => CallOK s stack 0 ∧ Ready H rt [n] s)
    (fun s s' => ∃ (buf : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
      s' = { s with regs := wbRegs s.regs junk buf, pc := s.regs 30, flags := f, vregs := v, mem := m } ∧
      MemFrame s.mem m (rt ++ [(s.sp.toNat - stack, s.sp.toNat - 8)]) ∧ WbSlots rt m buf.toNat n)

end Janus.Contracts

namespace Janus.Contracts

open Janus Janus.Amd64

/-! ## `gcWriteBarrierN` (amd64) -/

/-- **`runtime.gcWriteBarrierN`** (amd64, `N = n`): from a `CALL` (return address at `[RSP]`,
`[RSP - stack, RSP + 8)` writable) at which the runtime is ready, it returns with `RSP + 8`,
`R11` = the address of `8·n` fresh buffer bytes, every other general register, `X15`, the
direction flag and `FS` unchanged, the flags, `X0`–`X14` and the `YMM` upper halves
unspecified, memory changed only in `rt` and `[RSP - stack, RSP)`. -/
def WbContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) (n : Nat) : Prop :=
  Janus.Amd64.Tactic.Summary p addr (fun s => CallOK64 s stack 0 ∧ Ready64 H rt [n] s)
    (fun s s' => ∃ (buf : W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
      s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8#64 else if i = 11 then buf else s.regs i,
                    rip := Janus.Amd64.Tactic.retAddrOf s, flags := f,
                    xmm := fun i => if i = 15 then s.xmm 15 else x i, ymmHi := yh, mem := m } ∧
      MemFrame s.mem m (rt ++ [((s.regs 4).toNat - stack, (s.regs 4).toNat)]) ∧ WbSlots rt m buf.toNat n)

end Janus.Contracts
