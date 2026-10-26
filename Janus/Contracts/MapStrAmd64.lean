import Janus.Contracts.MapStr
import Janus.Contracts.MapVarAmd64

/-!
# String-keyed map entry points (amd64)

The amd64 counterparts of `Janus.Contracts.MapStr`: `RAX = t`, `RBX = m`, `RCX`/`RDI` the key's
data pointer and length; results in `RAX` and `RBX` (`ok`), the goroutine in `R14`. The
frame is `MapAmd64.RTReturn`.
-/

namespace Janus.Contracts.MapStr

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map Janus.Contracts.MapVar
open Janus (Outside InRanges)
open Janus.Contracts (RtReady rtView Ready64)

/-- **`runtime.mapaccess2_faststr(t, m, key)`** (amd64: `RAX = t`, `RBX = m`, `RCX`/`RDI` the
key's data pointer and length): as `Access2Str`; `ok` in `BL`. -/
def Access2Str64 (p : Janus.Amd64.Program) (addr : Nat) (M : MapModel (Nat × Nat) (BitVec 64)) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
      (s.regs 1).toNat + (s.regs 7).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 1).toNat (s.regs 7).toNat false = true ∧
      Outside (s.regs 1).toNat (s.regs 7).toNat (Contracts.MapAmd64.calleeStack s M.depth 4))
    (fun s s' => Contracts.MapAmd64.RTReturn M 4 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      Contracts.MapAmd64.SlotHolds M m (r 0).toNat
        ((f (strKey s.mem (s.regs 1).toNat (s.regs 7).toNat)).getD 0) ∧
      (r 3).toNat % 256 = (f (strKey s.mem (s.regs 1).toNat (s.regs 7).toNat)).isSome.toNat)

/-- The string key `(RCX, RDI)` is readable, below `2^48` and outside the callee's stack window
(amd64). -/
def StrIn64 (s : State) (d nargs : Nat) : Prop :=
  (s.regs 1).toNat + (s.regs 7).toNat ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 1).toNat (s.regs 7).toNat false = true ∧
    Outside (s.regs 1).toNat (s.regs 7).toNat (Contracts.MapAmd64.calleeStack s d nargs)

/-- **`runtime.mapaccess1_faststr(t, m, key)`** (amd64): as `Access1Str`. -/
def Access1Str64 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat)
    (M : MapModel (Nat × Nat) (BitVec (8 * vs))) : Prop :=
  ∀ f, Summary p addr
    (fun s => Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
      StrIn64 s M.depth 4)
    (fun s s' => Contracts.MapAmd64.RTReturn M 4 [] (s.regs 3).toNat s s' fun r m =>
      IsMap M m (s.regs 3).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (strKey s.mem (s.regs 1).toNat (s.regs 7).toNat)).getD 0).toNat)

/-- **`runtime.mapassign_faststr(t, m, key)`** (amd64): as `AssignStr`. -/
def AssignStr64 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat)
    (M : MapModel (Nat × Nat) (BitVec (8 * vs))) (H : RtReady) : Prop :=
  ∀ f, Summary p addr
    (fun s => Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 3).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 3).toNat f ∧ StrIn64 s M.depth 4 ∧
      StrOwned M (s.regs 1).toNat (s.regs 7).toNat ∧
      Ready64 H M.priv [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat, (s.regs 7).toNat] s)
    (fun s s' => Contracts.MapAmd64.RTReturn M 4 [] (s.regs 3).toNat s s' fun r m =>
      Contracts.MapAmd64.AssignSlot vs M (s.regs 3).toNat f
        (strKey s.mem (s.regs 1).toNat (s.regs 7).toNat) (s.regs 14) (r 0).toNat m)

/-- **`runtime.mapdelete_faststr(t, m, key)`** (amd64): as `DeleteStr`. -/
def DeleteStr64 (p : Janus.Amd64.Program) (addr : Nat) (vs : Nat)
    (M : MapModel (Nat × Nat) (BitVec (8 * vs))) : Prop :=
  ∀ f, Summary p addr
    (fun s => Contracts.MapAmd64.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 3).toNat f ∧
      StrIn64 s M.depth 4)
    (fun s s' => Contracts.MapAmd64.RTReturn M 4 [] (s.regs 3).toNat s s' fun _ m =>
      IsMap M m (s.regs 3).toNat (f.erase (strKey s.mem (s.regs 1).toNat (s.regs 7).toNat)))

end Janus.Contracts.MapStr

