import Janus.Contracts.Map
import Janus.Spec.Type

/-!
# Contracts of the remaining Go map entry points (arm64)

`Janus.Contracts.Map` states the `map[uint64]V` entry points (`_fast64`), `makemap_small`,
`mapclear` and iteration; `Janus.Contracts.MapStr` the string-keyed ones. This file states the
rest of what Go 1.26 lowers map operations to (`internal/runtime/maps`, `runtime/map.go`), all on
the **same abstract map** (`Janus.Spec.Map.AMap`, through a model `M : MapModel K V`): a theorem
that mixes, say, `mapassign_fast64ptr` and `mapaccess1_fast64` on one `map[*T]int` uses one
model, and every entry point's effect is stated on that model's `Rep`/`IsMap`.

| Go | Runtime call (Go 1.26) | Contract |
| --- | --- | --- |
| `make(map[K]V, n)`, `n` not a constant `≤ 8` | `runtime.makemap(t, n, nil) *Map` | `MakeMap` |
| `v := m[*kp]` (other key types) | `runtime.mapaccess1(t, m, kp) *V` | `Access1G` |
| `v, ok := m[*kp]` | `runtime.mapaccess2(t, m, kp) (*V, bool)` | `Access2G` |
| `m[*kp] = v` | `runtime.mapassign(t, m, kp) *V` | `AssignG` |
| `delete(m, *kp)` | `runtime.mapdelete(t, m, kp)` | `DeleteG` |
| `v := m[k]`, `V` over 1024 bytes | `runtime.mapaccess1_fat(t, m, kp, zero) *V` | `Access1Fat` |
| `v, ok := m[k]`, `V` over 1024 bytes | `runtime.mapaccess2_fat(t, m, kp, zero) (*V, bool)` | `Access2Fat` |
| `v := m[k]`, 4-byte `K` | `runtime.mapaccess1_fast32(t, m, k) *V` | `Access1F32` |
| `v, ok := m[k]`, 4-byte `K` | `runtime.mapaccess2_fast32(t, m, k) (*V, bool)` | `Access2F32` |
| `m[k] = v`, 4-byte `K` | `runtime.mapassign_fast32(t, m, k) *V` | `AssignF32` |
| `delete(m, k)`, 4-byte `K` | `runtime.mapdelete_fast32(t, m, k)` | `DeleteF32` |
| `m[k] = v`, `K` a pointer | `runtime.mapassign_fast64ptr(t, m, k) *V` | `Assign64Ptr` |

Values are `vs` bytes (`V = BitVec (8 · vs)`, the little-endian contents of the value slot): a
`map[uint32]bool` has `vs = 1`, a `map[K]int` has `vs = 8` (`BitVec (8 · 8)` is `BitVec 64`, so
these contracts share models with those of `Janus.Contracts.Map`).

**Generic keys, through the key type's hash and equality.** `mapaccess1`/`mapaccess2`/
`mapassign`/`mapdelete` hash the key with the map type's `Hasher` (`t.Hasher(key, m.seed)`) and
compare candidates with the key type's `Equal` (`t.Key.Equal`). Which keys are "the same" is
therefore decided by those two functions, not by the runtime's table code. The contracts here
are stated for key types whose descriptor has `TFlagRegularMemory` (`KeyRegular`: arrays and
structs of integers and pointers without padding, such as `[24]byte`): for them `Equal` is
`memequal` on the `n` key bytes and the hash is the seeded byte hash (`Hash.HashModel.regHash`,
an uninterpreted function of the seed and the bytes, `HashModel.Laws.regular`), so two keys are
the same exactly when their bytes are, and the abstract key is the bytes (`keyAt`). Key types
with floats (`+0 == -0`, `NaN != NaN`), strings or interfaces inside are not covered by these
contracts: their abstract key is not their bytes. The descriptor bytes are read in the runtime's
memory (`rtView M.priv`), where type descriptors live.

**Allocation.** `makemap` and every `mapassign*` allocate, so they take the readiness predicate
`H : RtReady` of round 9 (`Contracts.Ready H M.priv args s`): without it no code could meet
them (`audit/maps/model/Unsat.lean`).

**Not covered.** A nil map passed to `mapassign*` panics; the contracts require a non-nil map.
`makemap` with a non-nil `m` (a header the compiler placed on the caller's stack, for a map that
does not escape) is not covered: the map would live outside the runtime's memory. The key of an
access (`KeyIn`) must not lie in the callee's stack window, which the runtime's frames overwrite
before it reads the key.

The frame is `Map.RTReturn` (see `Janus.Contracts.Map`).
-/

namespace Janus.Contracts.MapVar

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts Janus.Contracts.Map

/-! ## Keys and values -/

/-- The value slot `p` (`vs` bytes) returned by an access: readable, in the runtime's memory,
holding `v`. -/
def SlotHoldsN {K V : Type} (M : MapModel K V) (m : Memory) (p vs v : Nat) : Prop :=
  m.accessible p vs false = true ∧ InRanges p vs M.priv ∧ m.readLE p vs = v

/-- The key type of the map type descriptor at `t` (`abi.MapType.Key`, offset 48). -/
def keyType (m : Memory) (t : Nat) : Nat := m.readLE (t + 48) 8

/-- The key type of the map type at `t` is `n` bytes of regular memory (`TFlagRegularMemory`):
its `Equal` compares the `n` bytes and its hash hashes them (see the module documentation). -/
def KeyRegular (m : Memory) (t n : Nat) : Prop :=
  tySize m (keyType m t) = n ∧ isRegularMemory m (keyType m t) = true

/-- The abstract key of the `n` key bytes at `kp`: their little-endian value. -/
def keyAt (m : Memory) (kp n : Nat) : BitVec (8 * n) := BitVec.ofNat (8 * n) (m.readLE kp n)

/-- The `n` key bytes at `kp` are readable, below `2^48`, and outside the stack window of a
callee with `nargs` register arguments and `d` bytes of stack (which its frames overwrite). -/
def KeyIn (s : State) (d nargs kp n : Nat) : Prop :=
  kp + n ≤ 2 ^ 48 ∧ s.mem.accessible kp n false = true ∧ Outside kp n (calleeStack s d nargs)

/-- A 4-byte key in `W2` (the upper half of `X2` is not part of the key). -/
def key32 (s : State) : BitVec 32 := (s.regs 2).setWidth 32

/-! ## `makemap` -/

/-- **`runtime.makemap(t, hint, nil)`** (`X0 = t`, `X1 = hint`, `X2 = 0`), when the runtime is
ready for the call: returns a new, non-nil, empty map (of any capacity: the hint only sizes the
tables), distinct from every map that existed before. -/
def MakeMap {K V : Type} (p : Program) (addr : Nat) (M : MapModel K V) (H : RtReady) : Prop :=
  Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 2).toNat = 0 ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, 0] s)
    (fun s s' => RTReturn M 3 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

/-! ## Generic keys (by pointer) -/

/-- **`runtime.mapaccess1(t, m, kp)`** for a key type of `n` bytes of regular memory: returns a
pointer to `m[*kp]`, or to a zero value (`runtime.zeroVal`) if absent or `m` is nil. -/
def Access1G (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (keyAt s.mem (s.regs 2).toNat n)).getD 0).toNat)

/-- **`runtime.mapaccess2(t, m, kp)`**: as `Access1G`, and the low byte of `X1` is `1` if the
key is present, `0` if not. -/
def Access2G (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (keyAt s.mem (s.regs 2).toNat n)).getD 0).toNat ∧
      (r 1).toNat % 256 = (f (keyAt s.mem (s.regs 2).toNat n)).isSome.toNat)

/-- **`runtime.mapassign(t, m, kp)`** on a non-nil map, when the runtime is ready for the call
(`H` sees the key's value as the fourth argument): returns the value slot of the key `*kp`
(`AssignSlot`); the runtime copies the key bytes into the map. -/
def AssignG (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      (s.regs 1).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat,
        s.mem.readLE (s.regs 2).toNat n] s)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 1).toNat f (keyAt s.mem (s.regs 2).toNat n) (s.regs 28) (r 0).toNat m)

/-- **`runtime.mapdelete(t, m, kp)`**: removes the key `*kp` (nothing happens for a nil map or
an absent key). -/
def DeleteG (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 3 (s.regs 2).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun _ m =>
      IsMap M m (s.regs 1).toNat (f.erase (keyAt s.mem (s.regs 2).toNat n)))

/-! ## Large values (`_fat`: the caller supplies the zero value) -/

/-- **`runtime.mapaccess1_fat(t, m, kp, zero)`** (`X3 = zero`, a zero value in the caller's
memory): returns a pointer to `m[*kp]` if present, else `zero`. -/
def Access1Fat (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 4 (s.regs 2).toNat n)
    (fun s s' => RTReturn M 4 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      (∀ v, f (keyAt s.mem (s.regs 2).toNat n) = some v → SlotHoldsN M m (r 0).toNat vs v.toNat) ∧
      (f (keyAt s.mem (s.regs 2).toNat n) = none → r 0 = s.regs 3))

/-- **`runtime.mapaccess2_fat(t, m, kp, zero)`**: as `Access1Fat`, and the low byte of `X1` is
`1` if the key is present, `0` if not. -/
def Access2Fat (p : Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 1).toNat f ∧ KeyIn s M.depth 4 (s.regs 2).toNat n)
    (fun s s' => RTReturn M 4 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      (∀ v, f (keyAt s.mem (s.regs 2).toNat n) = some v → SlotHoldsN M m (r 0).toNat vs v.toNat) ∧
      (f (keyAt s.mem (s.regs 2).toNat n) = none → r 0 = s.regs 3) ∧
      (r 1).toNat % 256 = (f (keyAt s.mem (s.regs 2).toNat n)).isSome.toNat)

/-! ## 4-byte keys (`_fast32`) -/

/-- **`runtime.mapaccess1_fast32(t, m, k)`** (`W2 = k`): returns a pointer to `m[k]`, or to a
zero value if absent or `m` is nil. -/
def Access1F32 (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧ SlotHoldsN M m (r 0).toNat vs ((f (key32 s)).getD 0).toNat)

/-- **`runtime.mapaccess2_fast32(t, m, k)`**: as `Access1F32`, and the low byte of `X1` is `1`
if `k` is present, `0` if not. -/
def Access2F32 (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧ SlotHoldsN M m (r 0).toNat vs ((f (key32 s)).getD 0).toNat ∧
      (r 1).toNat % 256 = (f (key32 s)).isSome.toNat)

/-- **`runtime.mapassign_fast32(t, m, k)`** on a non-nil map, when the runtime is ready for the
call: returns the value slot of `k` (`AssignSlot`). -/
def AssignF32 (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (key32 s).toNat] s)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 1).toNat f (key32 s) (s.regs 28) (r 0).toNat m)

/-- **`runtime.mapdelete_fast32(t, m, k)`**: removes `k` (nothing happens for a nil map or an
absent key). -/
def DeleteF32 (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun _ m =>
      IsMap M m (s.regs 1).toNat (f.erase (key32 s)))

/-! ## Pointer keys (`_fast64ptr`) -/

/-- **`runtime.mapassign_fast64ptr(t, m, k)`** (`X2 = k`, a pointer) on a non-nil map, when the
runtime is ready for the call: returns the value slot of `k` (`AssignSlot`). Lookups and
deletes of pointer-keyed maps use the `_fast64` entry points (`Map.Access1`, `Map.Access2`,
`Map.Delete`) on the same model. -/
def Assign64Ptr (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 64) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] s)
    (fun s s' => RTReturn M 3 [] (s.regs 1).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 1).toNat f (s.regs 2) (s.regs 28) (r 0).toNat m)

end Janus.Contracts.MapVar
