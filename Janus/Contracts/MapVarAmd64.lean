import Janus.Contracts.MapVar
import Janus.Contracts.MapAmd64

/-!
# Contracts of the remaining Go map entry points (amd64)

The amd64 counterparts of `Janus.Contracts.MapVar` (see that file and docs/RUNTIME-CONTRACTS.md,
"Maps"): the same entry points with the same effects on the same abstract map, stated with the
amd64 ABIInternal: `t` in `RAX`, the map in `RBX`, the key (or key pointer) in `RCX`, the
`_fat` zero value in `RDI`; results in `RAX` and `RBX` (`ok`); the goroutine in `R14`. The
frame is `MapAmd64.RTReturn`. The memory-level definitions (`SlotHoldsN`, `KeyRegular`,
`keyAt`) are `MapVar`'s.
-/

namespace Janus.Contracts.MapVarAmd64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Spec.Type
  Janus.Contracts.MapAmd64 Janus.Contracts.MapVar
open Janus (Outside InRanges)
open Janus.Contracts (RtReady rtView Ready64)

/-- The key bytes at `kp` are readable, below `2^48`, and outside the callee's stack window
(amd64). -/
def KeyIn (s : State) (d nargs kp n : Nat) : Prop :=
  kp + n ≤ 2 ^ 48 ∧ s.mem.accessible kp n false = true ∧ Outside kp n (MapAmd64.calleeStack s d nargs)

/-- A 4-byte key in `ECX`. -/
def key32 (s : State) : BitVec 32 := (s.regs 1).setWidth 32

/-! ## `makemap` -/

/-- **`runtime.makemap(t, hint, nil)`** (`RAX = t`, `RBX = hint`, `RCX = 0`), when the runtime is
ready for the call: returns a new, non-nil, empty map (of any capacity: the hint only sizes the
tables), distinct from every map that existed before. -/
def MakeMap {K V : Type} (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel K V) (H : RtReady) : Prop :=
  Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat = 0 ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, 0] s)
    (fun s s' => RTReturn M 3 [] 0 s s' fun r m =>
      (r 0).toNat ≠ 0 ∧ M.Rep m (r 0).toNat AMap.empty ∧
      ∀ mp f, M.Rep s.mem mp f → mp ≠ (r 0).toNat)

/-! ## Generic keys (by pointer) -/

/-- **`runtime.mapaccess1(t, m, kp)`** for a key type of `n` bytes of regular memory: returns a
pointer to `m[*kp]`, or to a zero value (`runtime.zeroVal`) if absent or `m` is nil. -/
def Access1G (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (keyAt s.mem (s.regs 1).toNat n)).getD 0).toNat)

/-- **`runtime.mapaccess2(t, m, kp)`**: as `Access1G`, and the low byte of `RBX` is `1` if the
key is present, `0` if not. -/
def Access2G (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (keyAt s.mem (s.regs 1).toNat n)).getD 0).toNat ∧
      (r 3).toNat % 256 = (f (keyAt s.mem (s.regs 1).toNat n)).isSome.toNat)

/-- **`runtime.mapassign(t, m, kp)`** on a non-nil map, when the runtime is ready for the call
(`H` sees the key's value as the fourth argument): returns the value slot of the key `*kp`
(`AssignSlot`); the runtime copies the key bytes into the map. -/
def AssignG (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      (s.regs 3).toNat ≠ 0 ∧ M.Rep s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat n ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat,
        s.mem.readLE (s.regs 1).toNat n] s)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 3).toNat f (keyAt s.mem (s.regs 1).toNat n) (s.regs 14) (r 0).toNat m)

/-- **`runtime.mapdelete(t, m, kp)`**: removes the key `*kp` (nothing happens for a nil map or
an absent key). -/
def DeleteG (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 3 (s.regs 1).toNat n)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun _ m =>
      IsMap M m (s.regs 3).toNat (f.erase (keyAt s.mem (s.regs 1).toNat n)))

/-! ## Large values (`_fat`: the caller supplies the zero value) -/

/-- **`runtime.mapaccess1_fat(t, m, kp, zero)`** (`RDI = zero`, a zero value in the caller's
memory): returns a pointer to `m[*kp]` if present, else `zero`. -/
def Access1Fat (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 4 (s.regs 1).toNat n)
    (fun s s' => RTReturn M 4 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      (∀ v, f (keyAt s.mem (s.regs 1).toNat n) = some v → SlotHoldsN M m (r 0).toNat vs v.toNat) ∧
      (f (keyAt s.mem (s.regs 1).toNat n) = none → r 0 = s.regs 7))

/-- **`runtime.mapaccess2_fat(t, m, kp, zero)`**: as `Access1Fat`, and the low byte of `RBX` is
`1` if the key is present, `0` if not. -/
def Access2Fat (p : Janus.Amd64.Program) (addr : Nat) (n vs : Nat) (M : MapModel (BitVec (8 * n)) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ KeyRegular (rtView M.priv s.mem) (s.regs 0).toNat n ∧
      IsMap M s.mem (s.regs 3).toNat f ∧ KeyIn s M.depth 4 (s.regs 1).toNat n)
    (fun s s' => RTReturn M 4 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      (∀ v, f (keyAt s.mem (s.regs 1).toNat n) = some v → SlotHoldsN M m (r 0).toNat vs v.toNat) ∧
      (f (keyAt s.mem (s.regs 1).toNat n) = none → r 0 = s.regs 7) ∧
      (r 3).toNat % 256 = (f (keyAt s.mem (s.regs 1).toNat n)).isSome.toNat)

/-! ## 4-byte keys (`_fast32`) -/

/-- **`runtime.mapaccess1_fast32(t, m, k)`** (`ECX = k`): returns a pointer to `m[k]`, or to a
zero value if absent or `m` is nil. -/
def Access1F32 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧ SlotHoldsN M m (r 0).toNat vs ((f (key32 s)).getD 0).toNat)

/-- **`runtime.mapaccess2_fast32(t, m, k)`**: as `Access1F32`, and the low byte of `RBX` is `1`
if `k` is present, `0` if not. -/
def Access2F32 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧ SlotHoldsN M m (r 0).toNat vs ((f (key32 s)).getD 0).toNat ∧
      (r 3).toNat % 256 = (f (key32 s)).isSome.toNat)

/-- **`runtime.mapassign_fast32(t, m, k)`** on a non-nil map, when the runtime is ready for the
call: returns the value slot of `k` (`AssignSlot`). -/
def AssignF32 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (key32 s).toNat] s)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 3).toNat f (key32 s) (s.regs 14) (r 0).toNat m)

/-- **`runtime.mapdelete_fast32(t, m, k)`**: removes `k` (nothing happens for a nil map or an
absent key). -/
def DeleteF32 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 32) (BitVec (8 * vs))) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun _ m =>
      IsMap M m (s.regs 3).toNat (f.erase (key32 s)))

/-! ## Pointer keys (`_fast64ptr`) -/

/-- **`runtime.mapassign_fast64ptr(t, m, k)`** (`RCX = k`, a pointer) on a non-nil map, when the
runtime is ready for the call: returns the value slot of `k` (`AssignSlot`). Lookups and
deletes of pointer-keyed maps use the `_fast64` entry points (`Map.Access1`, `Map.Access2`,
`Map.Delete`) on the same model. -/
def Assign64Ptr (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat) (M : MapModel (BitVec 64) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Janus.Amd64.Tactic.Summary p addr
    (fun s => RTPre M 3 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] s)
    (fun s s' => RTReturn M 3 [] (s.regs 3).toNat s s' fun r m =>
      AssignSlot vs M (s.regs 3).toNat f (s.regs 1) (s.regs 14) (r 0).toNat m)

end Janus.Contracts.MapVarAmd64
