import Janus.Contracts.String

/-!
# Runtime contracts: slices (arm64 and amd64)

The Go 1.26 slice helpers (`runtime/slice.go`, `runtime/mbarrier.go`) for **any element type**,
as ISA-independent `RtSpec`s (`Janus.Contracts.Rt`; `RtContract`/`RtContract64` make them
hypotheses). They complete the 8-byte-element `GrowsliceContract` of `Janus.Contracts.Alloc`:

| Go source | runtime entry | spec |
| --- | --- | --- |
| `append(s, …)` past `cap(s)` | `growslice(oldPtr, newLen, oldCap, num, et)` | `growsliceSpec` |
| the same, `s` known unaliased | `growsliceNoAlias` | `growsliceNoAliasSpec` |
| `append` into a stack buffer | `growsliceBuf(…, bufPtr, bufLen)`, `growsliceBufNoAlias` | `growsliceBufSpec` |
| `m := make([]T, n); copy(m, s)` | `makeslicecopy(et, tolen, fromlen, from)` | `makeslicecopySpec` |
| a stack-allocated slice escaping | `moveSlice`, `moveSliceNoScan`, `moveSliceNoCap`, `moveSliceNoCapNoScan` | `moveSlice*Spec` |
| `copy(dst, src)` (instrumented builds) | `slicecopy(to, toLen, from, fromLen, width)` | `slicecopySpec` |
| `copy(dst, src)`, pointerful elements | `typedslicecopy(typ, dst, dstLen, src, srcLen)` | `typedslicecopySpec` |

**Element types.** A type descriptor's `Size_` and `PtrBytes` (`typSize`, `typPtrBytes`) decide
the layout; `noscan` is `PtrBytes = 0`. The capacity `growslice` picks is
`growCap size noscan newLen oldCap = roundupsize (nextslicecap newLen oldCap · size) noscan / size`
for every element size: Go's four branches (size 1, pointer size, power of two, other) compute
the same number (the size classes are multiples of 8 and the page size a multiple of every
power of two up to it). The backing array holds the old elements; the bytes past the new length
are zero (pointer-free: `memclrNoHeapPointers`; pointerful: `mallocgc` zeroes the whole block,
so also the slots of the appended elements, which the caller overwrites).

**Write barriers.** With pointerful elements and the GC's write barrier on, the copying helpers
first call `bulkBarrierPreWrite*`, which only appends to the P's write-barrier buffer (runtime
memory, inside `rt`). The contracts hold for either value of the flag.

**`NoAlias`.** `growsliceNoAlias`/`growsliceBufNoAlias` free the old array only with
`GOEXPERIMENT=runtimefreegc`, which Go 1.26 does not enable; they are `growslice`/`growsliceBuf`.
-/

namespace Janus.Contracts

open Janus Janus.Arm64 Janus.Spec

/-- The capacity `growslice` returns for elements of `size` bytes (`noscan` if pointer-free). -/
def growCap (size : Nat) (noscan : Bool) (newLen oldCap : Nat) : Nat :=
  roundupsize (nextslicecap newLen oldCap * size) noscan / size

/-- `growCap8` is `growCap` for 8-byte pointer-free elements. -/
theorem growCap_eight (newLen oldCap : Nat) : growCap 8 true newLen oldCap = growCap8 newLen oldCap := rfl

/-- The capacity `growslice` picks holds at least `newLen` elements. -/
theorem le_growCap (size : Nat) (noscan : Bool) (newLen oldCap : Nat) (h : 0 < size) :
    newLen ≤ growCap size noscan newLen oldCap := by
  unfold growCap
  have h1 := le_roundupsize (nextslicecap newLen oldCap * size) noscan
  have h2 := le_nextslicecap newLen oldCap
  have : newLen * size ≤ roundupsize (nextslicecap newLen oldCap * size) noscan :=
    Nat.le_trans (Nat.mul_le_mul_right _ h2) h1
  exact (Nat.le_div_iff_mul_le h).2 this

/-- The element type at `et` is readable and has `size > 0` bytes, of which `PtrBytes ≤ size`
hold pointers. -/
def ElemOK (m : Memory) (et : Nat) : Prop :=
  TypeOK m et ∧ 0 < typSize m et ∧ typPtrBytes m et ≤ typSize m et

/-- `n` bytes at `p` are readable (nothing for `n = 0`). -/
def Readable (m : Memory) (p n : Nat) : Prop := p + n ≤ 2 ^ 48 ∧ (0 < n → m.accessible p n false = true)

/-- The new backing array `(r0, newLen, newCap)` of `growslice`: `newCap · size` bytes inside
`rt`, writable, the first `oldLen · size` bytes copied from `old`, the bytes from
`newLen · size` on zero (from `oldLen · size` on for a pointerful element type). -/
def GrownArray (rt : List (Nat × Nat)) (m0 m : Memory) (old oldLen newLen size : Nat) (noscan : Bool)
    (r0 newCap : Nat) : Prop :=
  InRanges r0 (newCap * size) rt ∧ r0 + newCap * size ≤ 2 ^ 48 ∧
    m.accessible r0 (newCap * size) true = true ∧
    (∀ i, i < oldLen * size → m.bytes (r0 + i) = m0.bytes (old + i)) ∧
    ZeroBytes m (r0 + newLen * size) (newCap * size - newLen * size) ∧
    (noscan = false → ZeroBytes m (r0 + oldLen * size) (newCap * size - oldLen * size))

/-- **`runtime.growslice(oldPtr, newLen, oldCap, num, et)`**: for `oldLen = newLen - num ≤ oldCap <
newLen` and `newLen · size < 2^46` (no panic path), returns `(ptr, newLen, newCap)` with
`newCap = growCap size noscan newLen oldCap` and a `GrownArray` at `ptr`. Words:
`oldPtr, newLen, oldCap, num, et`. -/
def growsliceSpec : RtSpec where
  nargs := 5
  pre a m := ElemOK m (arg a 4) ∧ arg a 3 ≤ arg a 1 ∧ arg a 1 - arg a 3 ≤ arg a 2 ∧
    arg a 2 < arg a 1 ∧ arg a 1 * typSize m (arg a 4) < 2 ^ 46 ∧
    Readable m (arg a 0) ((arg a 1 - arg a 3) * typSize m (arg a 4))
  reads a m := [(arg a 4, 16), (arg a 0, (arg a 1 - arg a 3) * typSize m (arg a 4))]
  post rt a m0 r0 r1 r2 m :=
    r1 = arg a 1 ∧
    r2 = growCap (typSize m0 (arg a 4)) (typNoscan m0 (arg a 4)) (arg a 1) (arg a 2) ∧
    GrownArray rt m0 m (arg a 0) (arg a 1 - arg a 3) (arg a 1) (typSize m0 (arg a 4))
      (typNoscan m0 (arg a 4)) r0 r2

/-- **`runtime.growsliceNoAlias`**: `growslice` (Go 1.26 frees nothing without
`GOEXPERIMENT=runtimefreegc`). -/
def growsliceNoAliasSpec : RtSpec := growsliceSpec

/-- The capacity `growsliceBuf` picks in the buffer: the next size class. -/
def bufCap (size : Nat) (noscan : Bool) (newLen : Nat) : Nat := roundupsize (newLen * size) noscan / size

/-- **`runtime.growsliceBuf(oldPtr, newLen, oldCap, num, et, bufPtr, bufLen)`**: as `growslice`
when `newLen > bufLen`; otherwise the stack buffer becomes the backing array: the old elements
are moved to its start (`memmove`), the capacity is `bufCap size noscan newLen`, and the bytes
from `newLen · size` to `cap · size` are zeroed; returns `(bufPtr, newLen, cap)`. The buffer
must hold `cap` elements (Go's compiler sizes it to a size class). Words: as `growslice`, then
`bufPtr, bufLen`. -/
def growsliceBufSpec : RtSpec where
  nargs := 7
  pre a m := growsliceSpec.pre a m ∧
    (arg a 1 ≤ arg a 6 → arg a 5 + bufCap (typSize m (arg a 4)) (typNoscan m (arg a 4)) (arg a 1) *
        typSize m (arg a 4) ≤ 2 ^ 48 ∧
      m.accessible (arg a 5) (bufCap (typSize m (arg a 4)) (typNoscan m (arg a 4)) (arg a 1) *
        typSize m (arg a 4)) true = true)
  writes a m := if arg a 1 ≤ arg a 6 then
    [(arg a 5, arg a 5 + bufCap (typSize m (arg a 4)) (typNoscan m (arg a 4)) (arg a 1) * typSize m (arg a 4))]
    else []
  reads a m := [(arg a 4, 16), (arg a 0, (arg a 1 - arg a 3) * typSize m (arg a 4))]
  post rt a m0 r0 r1 r2 m :=
    (arg a 6 < arg a 1 → growsliceSpec.post rt a m0 r0 r1 r2 m) ∧
    (arg a 1 ≤ arg a 6 → r0 = arg a 5 ∧ r1 = arg a 1 ∧
      r2 = bufCap (typSize m0 (arg a 4)) (typNoscan m0 (arg a 4)) (arg a 1) ∧
      (∀ i, i < (arg a 1 - arg a 3) * typSize m0 (arg a 4) → m.bytes (r0 + i) = m0.bytes (arg a 0 + i)) ∧
      ZeroBytes m (r0 + arg a 1 * typSize m0 (arg a 4)) (r2 * typSize m0 (arg a 4) - arg a 1 * typSize m0 (arg a 4)))

/-- **`runtime.growsliceBufNoAlias`**: `growsliceBuf` (see `growsliceNoAliasSpec`). -/
def growsliceBufNoAliasSpec : RtSpec := growsliceBufSpec

/-- **`runtime.makeslicecopy(et, tolen, fromlen, from)`** (`m := make([]T, tolen); copy(m,
from[:fromlen])`): returns a pointer to `tolen · size` fresh bytes inside `rt`, holding the
first `min(tolen, fromlen) · size` bytes of `from`, zero after. Words: `et, tolen, fromlen,
from`. -/
def makeslicecopySpec : RtSpec where
  nargs := 4
  pre a m := ElemOK m (arg a 0) ∧ arg a 1 * typSize m (arg a 0) ≤ maxAlloc ∧ arg a 1 < 2 ^ 63 ∧
    arg a 2 < 2 ^ 63 ∧ Readable m (arg a 3) (min (arg a 1) (arg a 2) * typSize m (arg a 0))
  reads a m := [(arg a 0, 16), (arg a 3, min (arg a 1) (arg a 2) * typSize m (arg a 0))]
  post rt a m0 r0 _ _ m :=
    let size := typSize m0 (arg a 0)
    0 < arg a 1 * size →
      InRanges r0 (arg a 1 * size) rt ∧ r0 + arg a 1 * size ≤ 2 ^ 48 ∧
      m.accessible r0 (arg a 1 * size) true = true ∧
      (∀ i, i < min (arg a 1) (arg a 2) * size → m.bytes (r0 + i) = m0.bytes (arg a 3 + i)) ∧
      ZeroBytes m (r0 + min (arg a 1) (arg a 2) * size) (arg a 1 * size - min (arg a 1) (arg a 2) * size)

/-- The result of `moveSlice*`: a fresh copy of `n` bytes from `old`, `capb` bytes in all, zero
from `n` on. -/
def MovedArray (rt : List (Nat × Nat)) (m0 m : Memory) (old n capb r0 : Nat) : Prop :=
  InRanges r0 capb rt ∧ r0 + capb ≤ 2 ^ 48 ∧ m.accessible r0 capb true = true ∧
    (∀ i, i < n → m.bytes (r0 + i) = m0.bytes (old + i)) ∧ ZeroBytes m (r0 + n) (capb - n)

/-- **`runtime.moveSlice(et, old, len, cap)`** (a stack-allocated slice moved to the heap):
`cap = 0` gives `(·, 0, 0)`; otherwise `(new, len, cap)` with `cap · size` bytes copied from
`old` into a fresh block. Words: `et, old, len, cap`. -/
def moveSliceSpec : RtSpec where
  nargs := 4
  pre a m := ElemOK m (arg a 0) ∧ arg a 2 ≤ arg a 3 ∧ arg a 3 * typSize m (arg a 0) ≤ maxAlloc ∧
    Readable m (arg a 1) (arg a 3 * typSize m (arg a 0))
  reads a m := [(arg a 0, 16), (arg a 1, arg a 3 * typSize m (arg a 0))]
  post rt a m0 r0 r1 r2 m :=
    (arg a 3 = 0 → r1 = 0 ∧ r2 = 0) ∧
    (0 < arg a 3 → r1 = arg a 2 ∧ r2 = arg a 3 ∧
      MovedArray rt m0 m (arg a 1) (arg a 3 * typSize m0 (arg a 0)) (arg a 3 * typSize m0 (arg a 0)) r0)

/-- **`runtime.moveSliceNoScan(elemSize, old, len, cap)`**: `moveSlice` for pointer-free elements of
`elemSize` bytes. Words: `elemSize, old, len, cap`. -/
def moveSliceNoScanSpec : RtSpec where
  nargs := 4
  pre a m := arg a 2 ≤ arg a 3 ∧ arg a 3 * arg a 0 ≤ maxAlloc ∧ Readable m (arg a 1) (arg a 3 * arg a 0)
  reads a _ := [(arg a 1, arg a 3 * arg a 0)]
  post rt a m0 r0 r1 r2 m :=
    (arg a 3 = 0 → r1 = 0 ∧ r2 = 0) ∧
    (0 < arg a 3 → r1 = arg a 2 ∧ r2 = arg a 3 ∧
      MovedArray rt m0 m (arg a 1) (arg a 3 * arg a 0) (arg a 3 * arg a 0) r0)

/-- **`runtime.moveSliceNoCap(et, old, len)`**: `len = 0` gives `(·, 0, 0)`; otherwise the `len`
elements in a fresh block of `roundupsize (len · size)` bytes (pointerful), capacity
`roundupsize (len · size) / size`, zero past the elements. Words: `et, old, len`. -/
def moveSliceNoCapSpec : RtSpec where
  nargs := 3
  pre a m := ElemOK m (arg a 0) ∧ arg a 2 * typSize m (arg a 0) ≤ maxAlloc ∧
    Readable m (arg a 1) (arg a 2 * typSize m (arg a 0))
  reads a m := [(arg a 0, 16), (arg a 1, arg a 2 * typSize m (arg a 0))]
  post rt a m0 r0 r1 r2 m :=
    let lenmem := arg a 2 * typSize m0 (arg a 0)
    (arg a 2 = 0 → r1 = 0 ∧ r2 = 0) ∧
    (0 < arg a 2 → r1 = arg a 2 ∧ r2 = roundupsize lenmem false / typSize m0 (arg a 0) ∧
      MovedArray rt m0 m (arg a 1) lenmem (roundupsize lenmem false) r0)

/-- **`runtime.moveSliceNoCapNoScan(elemSize, old, len)`**: `moveSliceNoCap` for pointer-free
elements of `elemSize > 0` bytes. Words: `elemSize, old, len`. -/
def moveSliceNoCapNoScanSpec : RtSpec where
  nargs := 3
  pre a m := 0 < arg a 0 ∧ arg a 2 * arg a 0 ≤ maxAlloc ∧ Readable m (arg a 1) (arg a 2 * arg a 0)
  reads a _ := [(arg a 1, arg a 2 * arg a 0)]
  post rt a m0 r0 r1 r2 m :=
    (arg a 2 = 0 → r1 = 0 ∧ r2 = 0) ∧
    (0 < arg a 2 → r1 = arg a 2 ∧ r2 = roundupsize (arg a 2 * arg a 0) true / arg a 0 ∧
      MovedArray rt m0 m (arg a 1) (arg a 2 * arg a 0) (roundupsize (arg a 2 * arg a 0) true) r0)

/-- The `n` bytes at `dst` are the `n` bytes that were at `src` (`memmove`, overlap allowed). -/
def Copied (m0 m : Memory) (dst src n : Nat) : Prop := ∀ i, i < n → m.bytes (dst + i) = m0.bytes (src + i)

/-- **`runtime.slicecopy(toPtr, toLen, fromPtr, fromLen, width)`**: copies
`n = min(toLen, fromLen)` elements of `width` bytes (none if either length is 0) and returns `n`.
Words: `toPtr, toLen, fromPtr, fromLen, width`. -/
def slicecopySpec : RtSpec where
  nargs := 5
  pre a m := arg a 1 < 2 ^ 63 ∧ arg a 3 < 2 ^ 63 ∧
    arg a 0 + min (arg a 1) (arg a 3) * arg a 4 ≤ 2 ^ 48 ∧
    (0 < min (arg a 1) (arg a 3) * arg a 4 → m.accessible (arg a 0) (min (arg a 1) (arg a 3) * arg a 4) true = true) ∧
    Readable m (arg a 2) (min (arg a 1) (arg a 3) * arg a 4)
  writes a _ := [(arg a 0, arg a 0 + min (arg a 1) (arg a 3) * arg a 4)]
  reads a _ := [(arg a 2, min (arg a 1) (arg a 3) * arg a 4)]
  post _ a m0 r0 _ _ m := r0 = min (arg a 1) (arg a 3) ∧
    Copied m0 m (arg a 0) (arg a 2) (min (arg a 1) (arg a 3) * arg a 4)

/-- **`runtime.typedslicecopy(typ, dstPtr, dstLen, srcPtr, srcLen)`** (`copy(dst, src)` for
elements with pointers): copies `n = min(dstLen, srcLen)` elements (with the write barrier's
bulk barrier first when the GC is marking) and returns `n`. Words: `typ, dst, dstLen, src,
srcLen`. -/
def typedslicecopySpec : RtSpec where
  nargs := 5
  pre a m := TypeOK m (arg a 0) ∧ arg a 2 < 2 ^ 63 ∧ arg a 4 < 2 ^ 63 ∧
    arg a 1 + min (arg a 2) (arg a 4) * typSize m (arg a 0) ≤ 2 ^ 48 ∧
    (0 < min (arg a 2) (arg a 4) * typSize m (arg a 0) →
      m.accessible (arg a 1) (min (arg a 2) (arg a 4) * typSize m (arg a 0)) true = true) ∧
    Readable m (arg a 3) (min (arg a 2) (arg a 4) * typSize m (arg a 0))
  writes a m := [(arg a 1, arg a 1 + min (arg a 2) (arg a 4) * typSize m (arg a 0))]
  reads a m := [(arg a 0, 16), (arg a 3, min (arg a 2) (arg a 4) * typSize m (arg a 0))]
  post _ a m0 r0 _ _ m := r0 = min (arg a 2) (arg a 4) ∧
    Copied m0 m (arg a 1) (arg a 3) (min (arg a 2) (arg a 4) * typSize m0 (arg a 0))

end Janus.Contracts
