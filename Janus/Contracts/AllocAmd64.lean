import Janus.Contracts.Alloc
import Janus.Amd64.Tactic
import Janus.Amd64.GoABI

/-!
# Runtime contracts: heap allocation (amd64)

The amd64 versions of the allocation contracts of `Janus.Contracts` (`Janus/Contracts/Alloc.lean`,
whose module documentation explains what they promise and why). The ISA-independent parts are
shared: `Fresh`, `blockSize`, `roundupsize`, `nextslicecap`, `growCap8`, `typSize`, `ZeroBytes`,
`InRanges`. What differs is the Go ABIInternal of amd64:

* arguments and results in `RAX, RBX, RCX, RDI, RSI, …`; at the call `[RSP]` holds the return
  address, the callee returns to it with `RSP + 8`;
* preserved across the call: `RSP` (popped by 8), `RBP` (frame pointer), `R14` (`g`), `X15` (zero),
  the direction flag and the `FS` base; every other general register, the flags, `X0`–`X14` and
  the upper halves of the `YMM` registers are unspecified;
* the callee may write `[RSP - stack, RSP)` below the stack pointer and the argument spill slots
  `[RSP + 8, RSP + 8 + 8·nargs)` of the caller's frame (`calleeStack64`); the return address at
  `[RSP, RSP + 8)` is preserved.

Every definition has the suffix `64`, so that a proof can open `Janus.Contracts` without
ambiguity.
-/

namespace Janus.Contracts

open Janus Janus.Amd64 Janus.Amd64.Tactic

attribute [janus64_exec, janus64_post] typSize typPtrBytes typNoscan maxAlloc true_implies mallocHdr
  minSizeForMallocHeader maxSmallSize mallocHeaderSize

/-- A 32-bit compare with zero of a loaded word (the write-barrier flag test `CMPL $0, …`) as
arithmetic, so that `janus64_run` can prune the branch with `omega`. -/
@[janus64_exec, janus64_post, janus_exec, janus_post] theorem ofNat32_readLE4_eq_zero
    (m : Janus.Arm64.Memory) (a : Nat) :
    (BitVec.ofNat 32 (m.readLE a 4) = 0#32) = (m.readLE a 4 = 0) := by
  apply propext
  have := Janus.Arm64.Memory.readLE_lt m a 4
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt (by simpa using this)]

/-- The general registers after a Go ABIInternal call (amd64) that returns `res` in
`RAX, RBX, RCX`: `RSP` is the call-time value plus 8 (the return address popped), `RBP` and
`R14` (`g`) keep their values, the result registers hold `res`, every other register `junk`. -/
def callRegs64 (old junk : Nat → W64) (res : List W64) : Nat → W64 :=
  fun i => if i = 4 then old 4 + 8#64 else if i = 5 ∨ i = 14 then old i
    else if i = 0 then res.getD 0 (junk 0) else if i = 3 then res.getD 1 (junk 3)
    else if i = 1 then res.getD 2 (junk 1) else junk i

@[janus64_exec, janus64_post] theorem callRegs64_apply (old junk : Nat → W64) (res : List W64)
    (i : Nat) : callRegs64 old junk res i =
      if i = 4 then old 4 + 8#64 else if i = 5 ∨ i = 14 then old i
      else if i = 0 then res.getD 0 (junk 0) else if i = 3 then res.getD 1 (junk 3)
      else if i = 1 then res.getD 2 (junk 1) else junk i := rfl

attribute [janus64_exec, janus64_post] getD_cons_zero getD_cons_lit getD_nil'

/-- The stack the callee may write (amd64): `[RSP - stack, RSP)` and the `nargs` spill slots
`[RSP + 8, RSP + 8 + 8·nargs)`; the return address at `[RSP, RSP + 8)` is preserved. -/
def calleeStack64 (s : State) (stack nargs : Nat) : List (Nat × Nat) :=
  [((s.regs 4).toNat - stack, (s.regs 4).toNat),
   ((s.regs 4).toNat + 8, (s.regs 4).toNat + 8 + 8 * nargs)]

/-- The ABI part of every contract precondition (amd64): the return address at `[RSP]` is below
`2^47` (a canonical user address: `RET` faults otherwise), `RSP` is 8-aligned, and `[RSP - stack, RSP + 8 + 8·nargs)` is writable and below
`2^48`. -/
def CallOK64 (s : State) (stack nargs : Nat) : Prop :=
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ (s.regs 4).toNat % 8 = 0 ∧
    stack ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible ((s.regs 4).toNat - stack) (stack + 8 + 8 * nargs) true = true

/-- The state a call returns in (amd64): registers by `callRegs64`, `rip` = the return address,
flags, `X0`–`X14`, the `YMM` upper halves and memory as given; `X15`, `FS` base and the direction
flag unchanged. -/
def retState64 (s : State) (junk : Nat → W64) (res : List W64) (f : Flags)
    (x : Nat → BitVec 128) (yh : Nat → BitVec 128) (m : Memory) : State :=
  { s with regs := callRegs64 s.regs junk res, rip := retAddrOf s, flags := f,
           xmm := fun i => if i = 15 then s.xmm 15 else x i, ymmHi := yh, mem := m }

attribute [janus64_exec, janus64_post] retState64 calleeStack64

/-- The readiness hypothesis of an amd64 contract at the call state `s` (round 9 C1, see
`Janus.Contracts.RtReady`): `H` holds for the call's arguments `args`, the current `g` (`R14`),
`RSP` and the runtime's memory (`rtView rt s.mem`). -/
@[reducible] def Ready64 (H : RtReady) (rt : List (Nat × Nat)) (args : List Nat) (s : State) :
    Prop :=
  H args (s.regs 14).toNat (s.regs 4).toNat (rtView rt s.mem)

attribute [janus64_exec, janus64_post] rtView_writeLE

/-- The shape of an allocation contract's postcondition (amd64), as `AllocRet`. -/
@[reducible] def AllocRet64 (rt : List (Nat × Nat)) (stack nargs : Nat) (res : W64 → List W64)
    (s s' : State) (Q : Memory → Nat → Prop) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Memory),
    s' = retState64 s junk (res ptr) f x yh m ∧
      MemFrame s.mem m (rt ++ calleeStack64 s stack nargs) ∧ Q m ptr.toNat

/-! Arguments: `RAX = regs 0`, `RBX = regs 3`, `RCX = regs 1`, `RDI = regs 7`, `RSI = regs 6`. -/

/-- The precondition of `runtime.mallocgc` (amd64; `RAX = size`, `RBX = typ` or nil,
`RCX = needzero` in its low byte). -/
def MallocgcPre64 (stack : Nat) (s : State) : Prop :=
  CallOK64 s stack 3 ∧ (s.regs 0).toNat ≤ maxAlloc ∧
    ((s.regs 3).toNat = 0 ∨ (TypeOK s.mem (s.regs 3).toNat ∧
      (typNoscan s.mem (s.regs 3).toNat = false → (s.regs 1).toNat % 256 ≠ 0)))

@[reducible] def mallocgcObj64 (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) :
    Prop :=
  Fresh rt m ptr (s.regs 0).toNat
    (blockSize (s.regs 0).toNat ((s.regs 3).toNat == 0 || typNoscan s.mem (s.regs 3).toNat))
    ((s.regs 1).toNat % 256 != 0 || ((s.regs 3).toNat != 0 && !typNoscan s.mem (s.regs 3).toNat))
    (mallocHdr (s.regs 0).toNat ((s.regs 3).toNat == 0 || typNoscan s.mem (s.regs 3).toNat))

/-- **`runtime.mallocgc(size, typ, needzero)`** (amd64): as `MallocgcContract`. -/
def MallocgcContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => MallocgcPre64 stack s ∧
      Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s)
    (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < (s.regs 0).toNat → mallocgcObj64 rt s m ptr)

theorem MallocgcContract64.pos {p : Janus.Amd64.Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : MallocgcContract64 p addr rt stack H) :
    Summary p addr (fun s => (MallocgcPre64 stack s ∧
        Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) ∧ 0 < (s.regs 0).toNat)
      (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' (mallocgcObj64 rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, h1, h2, h3 hp.2⟩

/-- The precondition of `runtime.newobject` (amd64; `RAX = typ`). -/
def NewobjectPre64 (stack : Nat) (s : State) : Prop :=
  CallOK64 s stack 1 ∧ TypeOK s.mem (s.regs 0).toNat ∧ typSize s.mem (s.regs 0).toNat ≤ maxAlloc

@[reducible] def newobjectObj64 (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) :
    Prop :=
  Fresh rt m ptr (typSize s.mem (s.regs 0).toNat)
    (blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)) true
    (mallocHdr (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat))

/-- **`runtime.newobject(typ)`** (amd64): as `NewobjectContract`. -/
def NewobjectContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => NewobjectPre64 stack s ∧ Ready64 H rt [(s.regs 0).toNat] s)
    (fun s s' => AllocRet64 rt stack 1 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < typSize s.mem (s.regs 0).toNat → newobjectObj64 rt s m ptr)

theorem NewobjectContract64.pos {p : Janus.Amd64.Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : NewobjectContract64 p addr rt stack H) :
    Summary p addr (fun s => (NewobjectPre64 stack s ∧ Ready64 H rt [(s.regs 0).toNat] s) ∧
      0 < typSize s.mem (s.regs 0).toNat)
      (fun s s' => AllocRet64 rt stack 1 (fun ptr => [ptr]) s s' (newobjectObj64 rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, h1, h2, h3 hp.2⟩

/-- The precondition of `runtime.makeslice` (amd64; `RAX = et`, `RBX = len`, `RCX = cap`). -/
def MakeslicePre64 (stack : Nat) (s : State) : Prop :=
  CallOK64 s stack 3 ∧ TypeOK s.mem (s.regs 0).toNat ∧
    (s.regs 3).toNat ≤ (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 63 ∧
    typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat ≤ maxAlloc

@[reducible] def makesliceObj64 (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) :
    Prop :=
  Fresh rt m ptr (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat)
    (blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat)
      (typNoscan s.mem (s.regs 0).toNat)) true
    (mallocHdr (typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat) (typNoscan s.mem (s.regs 0).toNat))

/-- **`runtime.makeslice(et, len, cap)`** (amd64): as `MakesliceContract`. -/
def MakesliceContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => MakeslicePre64 stack s ∧
      Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s)
    (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat → makesliceObj64 rt s m ptr)

theorem MakesliceContract64.pos {p : Janus.Amd64.Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : MakesliceContract64 p addr rt stack H) :
    Summary p addr
      (fun s => (MakeslicePre64 stack s ∧
        Ready64 H rt [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s) ∧
        0 < typSize s.mem (s.regs 0).toNat * (s.regs 1).toNat)
      (fun s s' => AllocRet64 rt stack 3 (fun ptr => [ptr]) s s' (makesliceObj64 rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, x, yh, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, x, yh, m, h1, h2, h3 hp.2⟩

/-- The arguments of `runtime.growslice` for 8-byte pointer-free elements (amd64;
`RAX = oldPtr`, `RBX = newLen`, `RCX = oldCap`, `RDI = num`, `RSI = et`). -/
def GrowsliceArgs64 (stack : Nat) (s : State) : Prop :=
  CallOK64 s stack 5 ∧ TypeOK s.mem (s.regs 6).toNat ∧
    typSize s.mem (s.regs 6).toNat = 8 ∧ typPtrBytes s.mem (s.regs 6).toNat = 0 ∧
    (s.regs 7).toNat ≤ (s.regs 3).toNat ∧
    (s.regs 3).toNat - (s.regs 7).toNat ≤ (s.regs 1).toNat ∧
    (s.regs 1).toNat < (s.regs 3).toNat ∧ (s.regs 3).toNat < 2 ^ 40

/-- The `oldLen` old elements at `oldPtr` are readable (amd64). -/
def GrowsliceOld64 (s : State) : Prop :=
  (s.regs 0).toNat + 8 * ((s.regs 3).toNat - (s.regs 7).toNat) ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (8 * ((s.regs 3).toNat - (s.regs 7).toNat)) false = true

def GrowslicePre64 (stack : Nat) (s : State) : Prop :=
  GrowsliceArgs64 stack s ∧ (0 < (s.regs 3).toNat - (s.regs 7).toNat → GrowsliceOld64 s)

@[reducible] def growsliceObj64 (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) :
    Prop :=
  Fresh rt m ptr (8 * growCap8 (s.regs 3).toNat (s.regs 1).toNat)
      (8 * growCap8 (s.regs 3).toNat (s.regs 1).toNat) false ∧
    (∀ i, i < 8 * ((s.regs 3).toNat - (s.regs 7).toNat) →
      m.bytes (ptr + i) = s.mem.bytes ((s.regs 0).toNat + i)) ∧
    ZeroBytes m (ptr + 8 * (s.regs 3).toNat)
      (8 * growCap8 (s.regs 3).toNat (s.regs 1).toNat - 8 * (s.regs 3).toNat)

/-- The arguments of a `growslice` call (amd64, `RAX, RBX, RCX, RDI, RSI`) as numbers. -/
@[reducible] def growsliceArgs64 (s : State) : List Nat :=
  [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat, (s.regs 6).toNat]

attribute [janus64_exec, janus64_post] growsliceArgs64

/-- **`runtime.growslice(oldPtr, newLen, oldCap, num, et)`** (amd64): as `GrowsliceContract`;
returns `(ptr, newLen, newCap)` in `RAX, RBX, RCX`. -/
def GrowsliceContract64 (p : Janus.Amd64.Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => GrowslicePre64 stack s ∧ Ready64 H rt (growsliceArgs64 s) s)
    (fun s s' => AllocRet64 rt stack 5
      (fun ptr => [ptr, s.regs 3, BitVec.ofNat 64 (growCap8 (s.regs 3).toNat (s.regs 1).toNat)])
      s s' (growsliceObj64 rt s))

theorem GrowsliceContract64.withOld {p : Janus.Amd64.Program} {addr : Nat} {rt : List (Nat × Nat)}
    {stack : Nat} {H : RtReady} (h : GrowsliceContract64 p addr rt stack H) :
    Summary p addr (fun s => (GrowsliceArgs64 stack s ∧ GrowsliceOld64 s) ∧
      Ready64 H rt (growsliceArgs64 s) s)
      (fun s s' => AllocRet64 rt stack 5
        (fun ptr => [ptr, s.regs 3, BitVec.ofNat 64 (growCap8 (s.regs 3).toNat (s.regs 1).toNat)])
        s s' (growsliceObj64 rt s)) :=
  Summary.mono h (fun _ h => ⟨⟨h.1.1, fun _ => h.1.2⟩, h.2⟩) fun _ _ _ h => h

theorem GrowsliceContract64.empty {p : Janus.Amd64.Program} {addr : Nat} {rt : List (Nat × Nat)}
    {stack : Nat} {H : RtReady} (h : GrowsliceContract64 p addr rt stack H) :
    Summary p addr (fun s => (GrowsliceArgs64 stack s ∧ (s.regs 3).toNat = (s.regs 7).toNat) ∧
      Ready64 H rt (growsliceArgs64 s) s)
      (fun s s' => AllocRet64 rt stack 5
        (fun ptr => [ptr, s.regs 3, BitVec.ofNat 64 (growCap8 (s.regs 3).toNat (s.regs 1).toNat)])
        s s' (growsliceObj64 rt s)) :=
  Summary.mono h (fun _ h => ⟨⟨h.1.1, fun h' => absurd h' (by omega)⟩, h.2⟩) fun _ _ _ h => h

end Janus.Contracts
