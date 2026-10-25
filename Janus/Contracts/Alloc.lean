import Lean
import Janus.Tactic
import Janus.Spec.Basic

/-!
# Runtime contracts: heap allocation (arm64)

A *runtime contract* is what a theorem assumes about a runtime function it calls but does not
execute. The extractor leaves the function out (`janus extract --contract runtime.newobject`,
recorded in `Program.contracts`), and the theorem is stated about `Extracted.program.link impl`
for **every** code `impl` placed at the contract addresses that satisfies the contract, which is
an ordinary `Tactic.Summary` hypothesis in the statement:

```
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [a, b]
      (fun s => pre rt s ∧ H [typ] (s.regs 28).toNat (s.sp.toNat - frame) (rtView rt s.mem)) post
```

So the printed statement shows exactly what is assumed, nothing is added to the trusted base,
and `janus_run calls [hnew]` uses the hypothesis at the `BL`. See docs/RUNTIME-CONTRACTS.md.

## What the allocation contracts say

All of them describe Go 1.26 `runtime.mallocgc` (`malloc.go`), reached through
`runtime.newobject(typ)` (`mallocgc(typ.Size_, typ, true)`), `runtime.makeslice(et, len, cap)`
(`mallocgc(et.Size_ * cap, et, true)`) and `runtime.growslice` (`slice.go`). From any state at
the entry that satisfies the precondition (an admissible return address in `X30`, an aligned
stack with the window the runtime may use writable, the type descriptor readable, the arguments
in range so that no panic path is taken) **and in which the runtime is ready for the call**
(`H`, see "The runtime's own state at a call" below: without it no code could meet the
contracts, round 9 C1), the function returns to `X30` with

* `X0` = a pointer `ptr` to a **fresh** object: `[ptr, ptr + blockSize size noscan)` lies inside
  one of the caller-declared **runtime-owned ranges** `rt`, is writable, below `2^48`, 8-aligned
  when `size ≥ 16` or a multiple of 8 (smaller pointer-free objects come from the tiny allocator) and 16-aligned when `size` is a multiple of 16 (Go's size classes: objects of a
  class are laid out from a page-aligned span base; every class except 8 and 24 is a multiple of
  16, large objects are page-aligned);
* the first `size` bytes **zero** when the call asks for zeroing (`needzero`, which `newobject`
  and `makeslice` always pass and which pointerful types always get);
* memory unchanged outside `rt` and the callee's stack window (`AllocFrame`: `[SP - stack, SP - 8)`
  below the stack pointer, and the argument spill slots `[SP + 8, SP + 8 + 8·nargs)` the callee may
  write in the caller's frame; the 8 bytes at `[SP - 8, SP)`, where Go's arm64 frame layout keeps
  the caller's saved frame pointer, are preserved), and every region's accessibility unchanged;
* `SP`, `R18`, `R28` (`g`) and `R29` (frame pointer) preserved; every other general register, the
  flags and the SIMD&FP registers unspecified (Go's ABIInternal has no other callee-saved register).

**Runtime-owned memory.** The runtime's own data (heap arenas and their free slots, `mcache`,
`mspan`s, `m`, `p`, the GC's buffers, its own stacks) is the caller-declared list `rt`. The
contract lets the allocator change anything inside `rt` and places the new object there; a
caller's precondition states that the data it uses (its arguments, its stack frame, the objects
it reads) lie outside `rt` (`Outside a n rt`). That is the honest form of "the runtime owns some
memory the program must not touch": a theorem says nothing about programs whose data overlaps
`rt`, and `rt` is a visible parameter of every statement. Freshness follows: the object is inside
`rt`, everything the caller holds is outside it.

**Regions.** Instructions never add a memory region in the model, so a contract that "adds a
region" could not be satisfied by any code and would make the theorem vacuous. Instead the arena
memory is already among `s.mem.regions` (Go reserves its heap arenas as address space up front;
mapping pages on demand is internal to the runtime) and the contract promises that the object is
writable there.

**Single allocation per runtime-owned list.** The contracts do not shrink `rt` after an
allocation: a second allocation may return memory overlapping the first one as far as these
contracts say. The example functions allocate once; a function that allocates twice needs a
contract over a state-dependent free set (see docs/RUNTIME-CONTRACTS.md).
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Tactic

/-! ## ISA-independent definitions (shared with `Janus.Contracts.Amd64`) -/

/-- Go 1.26 size classes (`internal/runtime/gc.SizeClassToSize`, class 0 omitted). -/
def sizeClasses : List Nat :=
  [8, 16, 24, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320,
   352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 896, 1024, 1152, 1280, 1408, 1536, 1792,
   2048, 2304, 2688, 3072, 3200, 3456, 4096, 4864, 5376, 6144, 6528, 6784, 6912, 8192, 9472,
   9728, 10240, 10880, 12288, 13568, 14336, 16384, 18432, 19072, 20480, 21760, 24576, 27264,
   28672, 32768]

/-- `maxSmallSize` (32 KiB): larger objects get their own span. -/
def maxSmallSize : Nat := 32768
/-- `gc.MallocHeaderSize`. -/
def mallocHeaderSize : Nat := 8
/-- `gc.MinSizeForMallocHeader` (`PtrSize * PtrBits`). -/
def minSizeForMallocHeader : Nat := 512
/-- The runtime page size (`pageSize`, 8 KiB). -/
def pageSize : Nat := 8192
/-- `maxAlloc` on linux/arm64 and linux/amd64 (`1 << heapAddrBits`, 48 bits). -/
def maxAlloc : Nat := 2 ^ 48

/-- The smallest size class holding `n` bytes (`n ≤ 32768`). This is what the runtime's tables
`SizeToSizeClass8`/`SizeToSizeClass128` compute (they are generated as exactly this lookup). -/
def classSize (n : Nat) : Nat := firstAtLeast sizeClasses n
where
  /-- The first element of the list that is at least `n` (`n` if there is none). -/
  firstAtLeast : List Nat → Nat → Nat
    | [], n => n
    | c :: cs, n => if n ≤ c then c else firstAtLeast cs n

/-- `runtime.roundupsize(size, noscan)` (`msize.go`): the size of the memory block `mallocgc`
allocates for `size` bytes, minus the inline malloc header of a pointerful object that needs
one. -/
def roundupsize (size : Nat) (noscan : Bool) : Nat :=
  if size ≤ maxSmallSize - mallocHeaderSize then
    let req := if !noscan && size > minSizeForMallocHeader then size + mallocHeaderSize else size
    classSize req - (req - size)
  else
    (size + pageSize - 1) / pageSize * pageSize

/-- `runtime.nextslicecap(newLen, oldCap)` (`slice.go`) for arguments without overflow: double a
small capacity, grow a large one by `(cap + 768)/4` until it reaches `newLen`. -/
def nextslicecap (newLen oldCap : Nat) : Nat :=
  if newLen > oldCap + oldCap then newLen
  else if oldCap < 256 then oldCap + oldCap
  else go oldCap
where
  go (c : Nat) : Nat :=
    let c' := c + (c + 3 * 256) / 4
    if c' ≥ newLen then c' else go c'
  termination_by newLen - c
  decreasing_by omega

/-- The bytes `mallocgc` promises the caller for a request of `size` bytes: the whole block
(`roundupsize`), except for a tiny allocation (pointer-free and below 16 bytes), which shares a
16-byte block with other tiny objects and owns only its `size` bytes. -/
def blockSize (size : Nat) (noscan : Bool) : Nat :=
  if noscan && size < 16 then size else roundupsize size noscan

theorem classSize_firstAtLeast_ge (cs : List Nat) (n : Nat) : n ≤ classSize.firstAtLeast cs n := by
  induction cs with
  | nil => exact Nat.le_refl _
  | cons c cs ih =>
    simp only [classSize.firstAtLeast]
    split
    · assumption
    · exact ih

theorem le_classSize (n : Nat) : n ≤ classSize n := classSize_firstAtLeast_ge _ _

/-- The block is at least the requested size. -/
theorem le_roundupsize (size : Nat) (noscan : Bool) : size ≤ roundupsize size noscan := by
  unfold roundupsize
  split
  · dsimp only
    generalize hreq : (if (!noscan && decide (size > minSizeForMallocHeader)) = true
      then size + mallocHeaderSize else size) = req
    have hge : size ≤ req := by rw [← hreq]; split <;> omega
    have := le_classSize req
    omega
  · have h := Nat.div_add_mod (size + pageSize - 1) pageSize
    have h2 := Nat.mod_lt (size + pageSize - 1) (show 0 < pageSize by decide)
    simp only [pageSize] at *
    omega

theorem classSize_firstAtLeast_le (cs : List Nat) (n b : Nat) (hn : n ≤ b) (hcs : ∀ c ∈ cs, c ≤ b) :
    classSize.firstAtLeast cs n ≤ b := by
  induction cs with
  | nil => exact hn
  | cons c cs ih =>
    simp only [classSize.firstAtLeast]
    split
    · exact hcs c (List.mem_cons_self ..)
    · exact ih fun c' h => hcs c' (List.mem_cons_of_mem _ h)

/-- A small request's block is at most `maxSmallSize` bytes. -/
theorem blockSize_le_maxSmallSize (size : Nat) (noscan : Bool) (h : size ≤ maxSmallSize) :
    blockSize size noscan ≤ maxSmallSize := by
  have hcs : ∀ c ∈ sizeClasses, c ≤ 32768 := by decide
  unfold blockSize roundupsize
  split
  · exact h
  · split
    · dsimp only
      generalize hreq : (if (!noscan && decide (size > minSizeForMallocHeader)) = true
        then size + mallocHeaderSize else size) = req
      have : req ≤ 32768 := by
        rw [← hreq]; simp only [maxSmallSize, mallocHeaderSize] at *; split <;> omega
      have := classSize_firstAtLeast_le sizeClasses req 32768 this hcs
      simp only [classSize, maxSmallSize] at *; omega
    · simp only [maxSmallSize, pageSize] at *
      have : (size + 8192 - 1) / 8192 ≤ 4 := by omega
      omega

theorem nextslicecap_go_ge (newLen c : Nat) : newLen ≤ nextslicecap.go newLen c := by
  induction c using nextslicecap.go.induct newLen with
  | case1 c c' h => rw [nextslicecap.go]; simp only [c'] at h; simp [h]
  | case2 c c' h ih => rw [nextslicecap.go]; simp only [c'] at h ih; simp [h, ih]

/-- `nextslicecap` reaches the requested length. -/
theorem le_nextslicecap (newLen oldCap : Nat) : newLen ≤ nextslicecap newLen oldCap := by
  unfold nextslicecap
  split
  · exact Nat.le_refl _
  · split
    · omega
    · exact nextslicecap_go_ge _ _

/-- Bytes `[a, a+n)` of `m` are zero. -/
def ZeroBytes (m : Memory) (a n : Nat) : Prop := ∀ i, i < n → m.bytes (a + i) = 0

theorem ZeroBytes.readLE {m : Memory} {a n : Nat} (h : ZeroBytes m a n) {k j : Nat}
    (hk : k + j ≤ n) : m.readLE (a + k) j = 0 := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    rw [Memory.readLE_succ, h k (by omega), show a + k + 1 = a + (k + 1) by omega,
      ih (k := k + 1) (by omega)]
    rfl

/-- Reads from a copy: if bytes `[a, a+n)` of `m'` are bytes `[b, b+n)` of `m`, so are the
`j`-byte reads at offset `k` (`k + j ≤ n`). -/
theorem readLE_of_copy {m m' : Memory} {a b n : Nat}
    (h : ∀ i, i < n → m'.bytes (a + i) = m.bytes (b + i)) {k j : Nat} (hk : k + j ≤ n) :
    m'.readLE (a + k) j = m.readLE (b + k) j := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    rw [Memory.readLE_succ, Memory.readLE_succ, h k (by omega),
      show a + k + 1 = a + (k + 1) by omega, show b + k + 1 = b + (k + 1) by omega,
      ih (k := k + 1) (by omega)]

/-- A range outside `rs` is disjoint from every range inside `rs`: what makes an object placed in
the runtime-owned ranges fresh for a caller whose data is outside them. -/
theorem _root_.Janus.InRanges.disjoint {a n b k : Nat} {rs : List (Nat × Nat)} (hin : InRanges a n rs)
    (hout : Outside b k rs) : b + k ≤ a ∨ a + n ≤ b := by
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem hout hr
  omega

/-- Does `mallocgc` place an 8-byte malloc header before the object? Go 1.26 does so for a
pointerful object of more than `minSizeForMallocHeader` (512) bytes that is still small
(`mallocgcSmallScanHeader`: the slot holds the type pointer, the object starts 8 bytes in), so
such an object is 8-aligned but **not** 16-aligned (round 9 C2). -/
def mallocHdr (size : Nat) (noscan : Bool) : Bool :=
  !noscan && decide (minSizeForMallocHeader < size) && decide (size ≤ maxSmallSize - mallocHeaderSize)

/-- What every allocation contract promises about the object at `ptr` in the returned memory
`m`: inside the runtime-owned ranges `rt`, below `2^48`, writable, aligned, and zeroed if asked.
`size` is the requested size, `round` the size of the block the caller may use (`blockSize`),
`hdr` whether the object follows a malloc header (`mallocHdr`: then it is 8-aligned only).
(A conjunction, `reducible`, so that `janus_run` splits it into hypotheses after the call.) -/
@[reducible] def Fresh (rt : List (Nat × Nat)) (m : Memory) (ptr size round : Nat) (zero : Bool)
    (hdr : Bool := false) : Prop :=
  InRanges ptr round rt ∧ ptr + round ≤ 2 ^ 48 ∧ m.accessible ptr round true = true ∧
    (16 ≤ size ∨ size % 8 = 0 → ptr % 8 = 0) ∧ (size % 16 = 0 → hdr = false → ptr % 16 = 0) ∧
    (zero = true → ZeroBytes m ptr size) ∧ size ≤ round

/-! ## The runtime's own state at a call (round 9 C1)

A contract is a `Summary`: a claim about **every** state at the function's entry that satisfies
its precondition. Before round 9 the precondition said nothing about the runtime's own state
(the heap, the `mcache`, the `g`), so the contract demanded that the allocator return a fresh,
writable object from states whose heap is not mapped at all, or whose request (up to `maxAlloc`,
`2^48` bytes) no memory could hold. No code meets that (the object must be writable in the
memory before the call, since instructions cannot add regions), so every theorem assuming such a
contract was vacuous (`audit/round9/model/Unsat.lean`); and the real runtime, which throws
`out of memory` for large requests and reads its own data structures, met it least of all.

Now every contract takes a **readiness predicate** `H : RtReady`, and its precondition also
requires `H args g sp (rtView rt s.mem)`: the call's arguments (as numbers), the current `g`
(arm64 `R28`, amd64 `R14`), the stack pointer at the call, and the memory **as the runtime owns
it** (`rtView`: the bytes inside `rt` and the regions; every other byte reads as 0). A theorem
quantifies over `H` and assumes it at its entry for the call it makes. So:

* the contract is satisfiable: a witness (an implementation, `rt` and `H`) is kernel-checked in
  `audit/round9/controls/`;
* the real runtime meets it with `H` := "from every call state with these arguments, this `g`,
  this `SP` and this runtime memory (whatever the memory outside `rt` holds), the runtime's code
  returns as the contract says" — by construction a function of what `H` sees, and true at the
  calls the allocator serves without a system call, a stack move or a throw (the common case:
  a free slot in the `mcache`, enough heap, no GC assist that parks);
* the caller's own stores (outside `rt`) do not change `rtView rt` (`rtView_writeLE`), so `H`
  carries from the entry of the function under proof to its call. -/

/-- `m` as the runtime sees it: its bytes inside the runtime-owned ranges `rt`, every other byte
`0`, and its regions. -/
def rtView (rt : List (Nat × Nat)) (m : Memory) : Memory :=
  { bytes := fun a => if rt.any (fun r => decide (r.1 ≤ a) && decide (a < r.2)) then m.bytes a else 0,
    regions := m.regions }

/-- A readiness predicate of the runtime: `H args g sp view` (see the section comment). -/
abbrev RtReady := List Nat → Nat → Nat → Memory → Prop

/-- A store outside the runtime-owned ranges does not change what the runtime sees. -/
@[janus_exec, janus_post] theorem rtView_writeLE {rt : List (Nat × Nat)} {m : Memory} {a n v : Nat}
    (h : Outside a n rt) : rtView rt (m.writeLE a n v) = rtView rt m := by
  unfold rtView
  congr 1
  funext x
  split
  · rename_i hx
    obtain ⟨r, hr, hx⟩ := List.any_eq_true.1 hx
    have := MemFrame.outside_mem h hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    exact Memory.bytes_writeLE_outside _ (by omega)
  · rfl

/-- Bytes inside `rt` read the same in the view. -/
theorem rtView_bytes {rt : List (Nat × Nat)} {m : Memory} {a : Nat} (h : InRanges a 1 rt) :
    (rtView rt m).bytes a = m.bytes a := by
  obtain ⟨r, hr, h1, h2⟩ := h
  simp only [rtView]
  rw [if_pos (List.any_eq_true.2 ⟨r, hr, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega⟩)]

/-- Reads inside `rt` are the same in the view. -/
theorem readLE_rtView {rt : List (Nat × Nat)} {m : Memory} {a n : Nat} (h : InRanges a n rt) :
    (rtView rt m).readLE a n = m.readLE a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    obtain ⟨r, hr, h1, h2⟩ := h
    rw [Memory.readLE_succ, Memory.readLE_succ, rtView_bytes ⟨r, hr, h1, by omega⟩,
      ih ⟨r, hr, by omega, by omega⟩]

/-- Zero bytes inside `rt` in the view are zero in memory. -/
theorem ZeroBytes.of_rtView {rt : List (Nat × Nat)} {m : Memory} {a n : Nat}
    (hz : ZeroBytes (rtView rt m) a n) (h : InRanges a n rt) : ZeroBytes m a n := by
  intro i hi
  obtain ⟨r, hr, h1, h2⟩ := h
  rw [← rtView_bytes (rt := rt) ⟨r, hr, by omega, by omega⟩]
  exact hz i hi

@[simp] theorem rtView_regions (rt : List (Nat × Nat)) (m : Memory) :
    (rtView rt m).regions = m.regions := rfl

@[simp] theorem rtView_accessible (rt : List (Nat × Nat)) (m : Memory) (a n : Nat) (w : Bool) :
    (rtView rt m).accessible a n w = m.accessible a n w := rfl

/-- A `CBZ W` on a loaded word (the write-barrier flag test) as arithmetic, so that `janus_run`
can prune the branch with `omega`. -/
@[janus_exec, janus_post] theorem setWidth_ofNat_eq_zero (w x : Nat) (hw : w ≤ 64) :
    (BitVec.setWidth w (BitVec.ofNat 64 x) = 0#w) = (x % 2 ^ w = 0) := by
  apply propext
  rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw)]

/-! 32-bit compares (`CMP Wn, Wm`, e.g. of the 16-bit `mspan` indices) as arithmetic, like the
64-bit flag lemmas of `Janus.Tactic`. -/

private theorem subRes32 (x y : BitVec 32) :
    (BitVec.ofNat 32 (x.toNat + (~~~y).toNat + true.toNat)).toNat =
      (x.toNat + 4294967296 - y.toNat) % 4294967296 := by
  simp only [BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  have := y.isLt; congr 1; omega

@[janus_exec, janus_post] theorem sub_flags_c32 (x y : BitVec 32) :
    (addSub x y true).2.c = decide (y.toNat ≤ x.toNat) := by
  simp only [addSub, addWithCarry, ite_true, subRes32]
  simp only [BitVec.toNat_not, Bool.toNat_true]
  have := x.isLt; have := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · rw [show x.toNat + 4294967296 - y.toNat = (x.toNat - y.toNat) + 4294967296 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [h]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]; simp [h]; omega

@[janus_exec, janus_post] theorem sub_flags_z32 (x y : BitVec 32) :
    (addSub x y true).2.z = decide (x.toNat = y.toNat) := by
  simp only [addSub, addWithCarry, ite_true]
  have hr := subRes32 x y
  have := x.isLt; have := y.isLt
  by_cases h : x.toNat = y.toNat
  · have : BitVec.ofNat 32 (x.toNat + (~~~y).toNat + true.toNat) = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hr]
      rw [show x.toNat + 4294967296 - y.toNat = 4294967296 by omega]; rfl
    rw [decide_eq_true this, decide_eq_true h]
  · have : BitVec.ofNat 32 (x.toNat + (~~~y).toNat + true.toNat) ≠ 0 := by
      intro h'; have h'' := congrArg BitVec.toNat h'; rw [hr] at h''; change _ = 0 at h''
      by_cases hle : y.toNat ≤ x.toNat
      · rw [show x.toNat + 4294967296 - y.toNat = (x.toNat - y.toNat) + 4294967296 by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h''; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h''; omega
    rw [decide_eq_false this, decide_eq_false h]

/-- The byte ranges `(base, length)` are pairwise disjoint. -/
def Separated : List (Nat × Nat) → Prop
  | [] => True
  | (a, n) :: rs => (∀ r ∈ rs, a + n ≤ r.1 ∨ r.1 + r.2 ≤ a) ∧ Separated rs

@[simp] theorem separated_nil : Separated [] = True := rfl
@[simp] theorem separated_cons (a n : Nat) (rs : List (Nat × Nat)) :
    Separated ((a, n) :: rs) = ((∀ r ∈ rs, a + n ≤ r.1 ∨ r.1 + r.2 ≤ a) ∧ Separated rs) := rfl

/-- The byte ranges `(base, length)` are pairwise `Apart`: the same as `Separated`, in the form
`omega` does not case-split on (the dischargers use one `Apart` fact at a time, `janus_apart`).
Use it for preconditions that relate many objects. -/
def Spread : List (Nat × Nat) → Prop
  | [] => True
  | (a, n) :: rs => (∀ r ∈ rs, Apart a n r.1 r.2) ∧ Spread rs

@[simp] theorem spread_nil : Spread [] = True := rfl
@[simp] theorem spread_cons (a n : Nat) (rs : List (Nat × Nat)) :
    Spread ((a, n) :: rs) = ((∀ r ∈ rs, Apart a n r.1 r.2) ∧ Spread rs) := rfl

/-! ## arm64 -/

/-- The general registers after a Go ABIInternal call (arm64) that returns `res` in `X0, X1, …`:
`R18`, `R28` (`g`) and `R29` (frame pointer) keep their values from `old`, the result registers
hold `res`, every other register the unspecified `junk`. -/
def callRegs (old junk : Nat → W64) (res : List W64) : Nat → W64 :=
  fun i => if i = 18 ∨ i = 28 ∨ i = 29 then old i else res.getD i (junk i)

@[janus_exec, janus_post] theorem callRegs_apply (old junk : Nat → W64) (res : List W64) (i : Nat) :
    callRegs old junk res i = if i = 18 ∨ i = 28 ∨ i = 29 then old i else res.getD i (junk i) := rfl

@[janus_exec, janus_post] theorem getD_cons_zero {α} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a := rfl
@[janus_exec, janus_post] theorem getD_cons_lit {α} (a : α) (l : List α) (d : α) (n : Nat)
    [NeZero n] : (a :: l).getD n d = l.getD (n - 1) d := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  rfl
@[janus_exec, janus_post] theorem getD_nil' {α} (n : Nat) (d : α) : ([] : List α).getD n d = d := by
  cases n <;> rfl

/-- The stack the callee may write (arm64): `[SP - stack, SP - 8)` below the stack pointer (the
caller's saved frame pointer at `[SP - 8, SP)` is preserved) and the `nargs` argument spill slots
`[SP + 8, SP + 8 + 8·nargs)` in the caller's frame. -/
def calleeStack (s : State) (stack nargs : Nat) : List (Nat × Nat) :=
  [(s.sp.toNat - stack, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 8 + 8 * nargs)]

/-- The ABI part of every contract precondition (arm64): `X30` is an admissible return address
(4-aligned, below `2^48`), `SP` is 16-aligned, and the stack window `[SP - stack, SP + 8 + 8·nargs)`
is writable and below `2^48`. -/
def CallOK (s : State) (stack nargs : Nat) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ s.sp.toNat % 16 = 0 ∧
    stack ≤ s.sp.toNat ∧ 8 ≤ stack ∧ s.sp.toNat + 8 + 8 * nargs ≤ 2 ^ 48 ∧
    s.mem.accessible (s.sp.toNat - stack) (stack + 8 + 8 * nargs) true = true

/-- `typ.Size_` of the `abi.Type` at `typ` (offset 0). -/
def typSize (m : Memory) (typ : Nat) : Nat := m.readLE typ 8
/-- `typ.PtrBytes` (offset 8): the type has pointers iff it is non-zero. -/
def typPtrBytes (m : Memory) (typ : Nat) : Nat := m.readLE (typ + 8) 8
/-- `!typ.Pointers()`. -/
def typNoscan (m : Memory) (typ : Nat) : Bool := typPtrBytes m typ == 0

attribute [janus_exec, janus_post] typSize typPtrBytes typNoscan maxAlloc mallocHdr minSizeForMallocHeader maxSmallSize mallocHeaderSize

/-- The type descriptor at `typ` is readable (its `Size_` and `PtrBytes` words). -/
def TypeOK (m : Memory) (typ : Nat) : Prop :=
  typ + 16 ≤ 2 ^ 48 ∧ m.accessible typ 16 false = true

/-- The state a call returns in (arm64): registers by `callRegs`, `pc = X30`, flags, SIMD&FP
registers and memory as given; `SP`, `dczid`, `tpidr` unchanged. -/
def retState (s : State) (junk : Nat → W64) (res : List W64) (f : Flags)
    (v : Nat → BitVec 128) (m : Memory) : State :=
  { s with regs := callRegs s.regs junk res, pc := s.regs 30, flags := f, vregs := v, mem := m }

attribute [janus_exec, janus_post] retState calleeStack

/-- The readiness hypothesis of an arm64 contract at the call state `s` (round 9 C1): `H` holds
for the call's arguments `args`, the current `g` (`R28`), `SP` and the runtime's memory
(`rtView rt s.mem`). -/
@[reducible] def Ready (H : RtReady) (rt : List (Nat × Nat)) (args : List Nat) (s : State) : Prop :=
  H args (s.regs 28).toNat s.sp.toNat (rtView rt s.mem)

open Lean Meta in
/-- `blockSize n b` for literal `n` and `b` evaluates to its value (a definitional unfolding the
kernel re-checks); for a symbolic size it stays folded (unfolding it would split on all 67 size
classes). -/
dsimproc reduceBlockSize (blockSize _ _) := fun e => do
  let_expr blockSize n b := e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some b := (match b.constName? with
    | some ``Bool.true => some true | some ``Bool.false => some false | _ => none) |
    return .continue
  return .done (toExpr (blockSize n b))
attribute [janus_exec, janus_post] true_implies

/-- The shape of an allocation contract's postcondition (arm64): the callee returned to `X30`
in `retState s junk (res ptr) f v m` for some pointer `ptr`, unspecified registers, flags and
SIMD&FP registers, and memory `m` that differs from `s.mem` only inside the runtime-owned
ranges `rt` and the callee's stack window, and `Q m ptr` holds. -/
@[reducible] def AllocRet (rt : List (Nat × Nat)) (stack nargs : Nat) (res : W64 → List W64)
    (s s' : State) (Q : Memory → Nat → Prop) : Prop :=
  ∃ (ptr : W64) (junk : Nat → W64) (f : Flags) (v : Nat → BitVec 128) (m : Memory),
    s' = retState s junk (res ptr) f v m ∧ MemFrame s.mem m (rt ++ calleeStack s stack nargs) ∧
      Q m ptr.toNat

/-- The precondition of `runtime.mallocgc` (arm64): see `MallocgcContract`. -/
def MallocgcPre (stack : Nat) (s : State) : Prop :=
  CallOK s stack 3 ∧ (s.regs 0).toNat ≤ maxAlloc ∧
    ((s.regs 1).toNat = 0 ∨ (TypeOK s.mem (s.regs 1).toNat ∧
      (typNoscan s.mem (s.regs 1).toNat = false → (s.regs 2).toNat % 256 ≠ 0)))

/-- `mallocgc`'s object for the call state `s`: `X0` bytes, block `blockSize`, zeroed when
`needzero` (`X2`'s low byte) or the type has pointers. -/
@[reducible] def mallocgcObj (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) : Prop :=
  Fresh rt m ptr (s.regs 0).toNat
    (blockSize (s.regs 0).toNat ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat))
    ((s.regs 2).toNat % 256 != 0 || ((s.regs 1).toNat != 0 && !typNoscan s.mem (s.regs 1).toNat))
    (mallocHdr (s.regs 0).toNat ((s.regs 1).toNat == 0 || typNoscan s.mem (s.regs 1).toNat))

/-- **`runtime.mallocgc(size, typ, needzero)`** (arm64; `X0 = size`, `X1 = typ` or nil,
`X2 = needzero` in its low byte). For `size > 0` the result is a fresh object of
`blockSize size noscan` bytes, zeroed if `needzero` or the type has pointers; `size = 0` returns
`&runtime.zerobase`, about which nothing is promised. A pointerful `typ` with `needzero = false`
makes the runtime throw, so the precondition excludes it. The runtime must be ready for the call
(`Ready H rt [size, typ, needzero]`, round 9 C1). -/
def MallocgcContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => MallocgcPre stack s ∧
      Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s)
    (fun s s' => AllocRet rt stack 3 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < (s.regs 0).toNat → mallocgcObj rt s m ptr)

/-- `MallocgcContract` at a call of non-zero size. -/
theorem MallocgcContract.pos {p : Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : MallocgcContract p addr rt stack H) :
    Summary p addr (fun s => (MallocgcPre stack s ∧
        Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) ∧ 0 < (s.regs 0).toNat)
      (fun s s' => AllocRet rt stack 3 (fun ptr => [ptr]) s s' (mallocgcObj rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, v, m, h1, h2, h3 hp.2⟩

/-- The precondition of `runtime.newobject` (arm64): see `NewobjectContract`. -/
def NewobjectPre (stack : Nat) (s : State) : Prop :=
  CallOK s stack 1 ∧ TypeOK s.mem (s.regs 0).toNat ∧ typSize s.mem (s.regs 0).toNat ≤ maxAlloc

/-- `newobject`'s object: `typ.Size_` bytes, zeroed. -/
@[reducible] def newobjectObj (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) : Prop :=
  Fresh rt m ptr (typSize s.mem (s.regs 0).toNat)
    (blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)) true
    (mallocHdr (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat))

/-- **`runtime.newobject(typ)`** (arm64; `X0 = typ`): `mallocgc(typ.Size_, typ, true)`, a fresh
zeroed object of `typ.Size_` bytes (for a non-zero size), when the runtime is ready for the call
(`Ready H rt [typ]`, round 9 C1). -/
def NewobjectContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => NewobjectPre stack s ∧ Ready H rt [(s.regs 0).toNat] s)
    (fun s s' => AllocRet rt stack 1 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < typSize s.mem (s.regs 0).toNat → newobjectObj rt s m ptr)

/-- `NewobjectContract` for a type of non-zero size. -/
theorem NewobjectContract.pos {p : Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : NewobjectContract p addr rt stack H) :
    Summary p addr (fun s => (NewobjectPre stack s ∧ Ready H rt [(s.regs 0).toNat] s) ∧
      0 < typSize s.mem (s.regs 0).toNat)
      (fun s s' => AllocRet rt stack 1 (fun ptr => [ptr]) s s' (newobjectObj rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, v, m, h1, h2, h3 hp.2⟩

/-- The precondition of `runtime.makeslice` (arm64): see `MakesliceContract`. -/
def MakeslicePre (stack : Nat) (s : State) : Prop :=
  CallOK s stack 3 ∧ TypeOK s.mem (s.regs 0).toNat ∧
    (s.regs 1).toNat ≤ (s.regs 2).toNat ∧ (s.regs 2).toNat < 2 ^ 63 ∧
    typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat ≤ maxAlloc

/-- `makeslice`'s block: `et.Size_ · cap` bytes, zeroed. -/
@[reducible] def makesliceObj (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) : Prop :=
  Fresh rt m ptr (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat)
    (blockSize (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat)
      (typNoscan s.mem (s.regs 0).toNat)) true
    (mallocHdr (typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat) (typNoscan s.mem (s.regs 0).toNat))

/-- **`runtime.makeslice(et, len, cap)`** (arm64; `X0 = et`, `X1 = len`, `X2 = cap`), for
arguments that take no panic path (`0 ≤ len ≤ cap < 2^63`, `et.Size_ · cap ≤ maxAlloc`; the panic
paths `panicmakeslicelen`/`panicmakeslicecap` are excluded by the precondition rather than
specified): a fresh zeroed block of `et.Size_ · cap` bytes (for a non-zero size), when the runtime
is ready for the call (`Ready H rt [et, len, cap]`, round 9 C1). -/
def MakesliceContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => MakeslicePre stack s ∧
      Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s)
    (fun s s' => AllocRet rt stack 3 (fun ptr => [ptr]) s s' fun m ptr =>
      0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat → makesliceObj rt s m ptr)

/-- `MakesliceContract` for a block of non-zero size. -/
theorem MakesliceContract.pos {p : Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : MakesliceContract p addr rt stack H) :
    Summary p addr
      (fun s => (MakeslicePre stack s ∧
        Ready H rt [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s) ∧
        0 < typSize s.mem (s.regs 0).toNat * (s.regs 2).toNat)
      (fun s s' => AllocRet rt stack 3 (fun ptr => [ptr]) s s' (makesliceObj rt s)) :=
  Summary.mono h (fun _ h => h.1) fun _ _ hp ⟨ptr, j, f, v, m, h1, h2, h3⟩ =>
    ⟨ptr, j, f, v, m, h1, h2, h3 hp.2⟩

/-- The capacity `growslice` returns for 8-byte elements without pointers. -/
def growCap8 (newLen oldCap : Nat) : Nat := roundupsize (nextslicecap newLen oldCap * 8) true / 8

/-- The capacity `growslice` returns holds the new length. -/
theorem le_growCap8 (newLen oldCap : Nat) : newLen ≤ growCap8 newLen oldCap := by
  unfold growCap8
  have h1 := le_nextslicecap newLen oldCap
  have h2 := le_roundupsize (nextslicecap newLen oldCap * 8) true
  exact (Nat.le_div_iff_mul_le (by decide)).2 (by omega)

/-- The arguments of `runtime.growslice` for 8-byte pointer-free elements (arm64): the ABI part,
the element type, and `oldLen = newLen - num ≤ oldCap < newLen < 2^40` (no panic path). -/
def GrowsliceArgs (stack : Nat) (s : State) : Prop :=
  CallOK s stack 5 ∧ TypeOK s.mem (s.regs 4).toNat ∧
    typSize s.mem (s.regs 4).toNat = 8 ∧ typPtrBytes s.mem (s.regs 4).toNat = 0 ∧
    (s.regs 3).toNat ≤ (s.regs 1).toNat ∧
    (s.regs 1).toNat - (s.regs 3).toNat ≤ (s.regs 2).toNat ∧
    (s.regs 2).toNat < (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 40

/-- The `oldLen` old elements at `oldPtr` are readable. -/
def GrowsliceOld (s : State) : Prop :=
  (s.regs 0).toNat + 8 * ((s.regs 1).toNat - (s.regs 3).toNat) ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 0).toNat (8 * ((s.regs 1).toNat - (s.regs 3).toNat)) false = true

/-- The precondition of `runtime.growslice` for 8-byte pointer-free elements (arm64): the
arguments, and the old elements readable when there are any (`append(nil, x)` passes a nil
`oldPtr`). -/
def GrowslicePre (stack : Nat) (s : State) : Prop :=
  GrowsliceArgs stack s ∧ (0 < (s.regs 1).toNat - (s.regs 3).toNat → GrowsliceOld s)

/-- `growslice`'s new backing array for the call state `s` (8-byte pointer-free elements):
`8·newCap` bytes, fresh, holding the `oldLen` old elements, zero from `8·newLen` on. -/
@[reducible] def growsliceObj (rt : List (Nat × Nat)) (s : State) (m : Memory) (ptr : Nat) :
    Prop :=
  Fresh rt m ptr (8 * growCap8 (s.regs 1).toNat (s.regs 2).toNat)
      (8 * growCap8 (s.regs 1).toNat (s.regs 2).toNat) false ∧
    (∀ i, i < 8 * ((s.regs 1).toNat - (s.regs 3).toNat) →
      m.bytes (ptr + i) = s.mem.bytes ((s.regs 0).toNat + i)) ∧
    ZeroBytes m (ptr + 8 * (s.regs 1).toNat)
      (8 * growCap8 (s.regs 1).toNat (s.regs 2).toNat - 8 * (s.regs 1).toNat)

/-- The arguments of a `growslice` call (arm64, `X0 … X4`) as numbers. -/
@[reducible] def growsliceArgs (s : State) : List Nat :=
  [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat, (s.regs 4).toNat]

attribute [janus_exec, janus_post] growsliceArgs

/-- **`runtime.growslice(oldPtr, newLen, oldCap, num, et)`** (arm64; `X0 … X4`), for an element
type of 8 bytes without pointers (`et.Size_ = 8`, `et.PtrBytes = 0`, e.g. `uint64`), with
`oldLen = newLen - num`, `oldLen ≤ oldCap < newLen < 2^40` (no panic path) and the `oldLen` old
elements readable. Returns `(ptr, newLen, newCap)` in `X0, X1, X2` with
`newCap = growCap8 newLen oldCap` (Go's growth rule `nextslicecap` and the size-class rounding
`roundupsize`); the block of `8·newCap` bytes at `ptr` is fresh, its first `8·oldLen` bytes are
the old elements (`memmove`), the bytes from `8·newLen` to `8·newCap` are zero
(`memclrNoHeapPointers`), and the bytes of the `num` new elements are unspecified (the caller
writes them). Other element types are not covered by this contract. The runtime must be ready for
the call (`Ready H rt [oldPtr, newLen, oldCap, num, et]`, round 9 C1). -/
def GrowsliceContract (p : Program) (addr : Nat) (rt : List (Nat × Nat)) (stack : Nat)
    (H : RtReady) : Prop :=
  Summary p addr (fun s => GrowslicePre stack s ∧ Ready H rt (growsliceArgs s) s)
    (fun s s' => AllocRet rt stack 5
      (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
      s s' (growsliceObj rt s))

/-- `GrowsliceContract` at a call whose old elements are readable. -/
theorem GrowsliceContract.withOld {p : Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : GrowsliceContract p addr rt stack H) :
    Summary p addr (fun s => (GrowsliceArgs stack s ∧ GrowsliceOld s) ∧ Ready H rt (growsliceArgs s) s)
      (fun s s' => AllocRet rt stack 5
        (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
        s s' (growsliceObj rt s)) :=
  Summary.mono h (fun _ h => ⟨⟨h.1.1, fun _ => h.1.2⟩, h.2⟩) fun _ _ _ h => h

/-- `GrowsliceContract` at a call with no old elements (`newLen = num`). -/
theorem GrowsliceContract.empty {p : Program} {addr : Nat} {rt : List (Nat × Nat)} {stack : Nat}
    {H : RtReady} (h : GrowsliceContract p addr rt stack H) :
    Summary p addr (fun s => (GrowsliceArgs stack s ∧ (s.regs 1).toNat = (s.regs 3).toNat) ∧
      Ready H rt (growsliceArgs s) s)
      (fun s s' => AllocRet rt stack 5
        (fun ptr => [ptr, s.regs 1, BitVec.ofNat 64 (growCap8 (s.regs 1).toNat (s.regs 2).toNat)])
        s s' (growsliceObj rt s)) :=
  Summary.mono h (fun _ h => ⟨⟨h.1.1, fun h' => absurd h' (by omega)⟩, h.2⟩) fun _ _ _ h => h

end Janus.Contracts
