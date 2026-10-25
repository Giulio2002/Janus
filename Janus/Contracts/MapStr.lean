import Janus.Contracts.Hash
import Janus.Contracts.HashAmd64
import Janus.Contracts.EqHashModel

/-!
# String-keyed map lookup (`runtime.mapaccess2_faststr`, arm64 and amd64)

A `map[string]V` keys its entries by the strings' contents: two strings with the same length
and bytes are the same key whatever their data pointers (Go's `==`, `Mem.strEq`). That is what
makes the runtime's lookup correct: it hashes the key with `strhash`, whose result depends only
on the length and the bytes (`Hash.Strhash`; equal strings hash alike,
`HashLaws.strhash_of_strEq`), and compares the candidates in the probed group with string
equality. So the abstract map of `Janus.Spec.Map` is keyed here by the content
`strKey m p n = (n, bytes)`, and `strKey_eq_of_strEq` turns Go's string equality into equality of
keys. Further string-keyed entry points (`mapassign_faststr`, `mapdelete_faststr`, …) are work
package R3.

The contracts have the frame of `Janus.Contracts.Map` (`Map.RTPre`, `Map.RTReturn`; amd64
`MapAmd64.RTPre`, `MapAmd64.RTReturn`). Their satisfiability (`access2Str_satisfiable`,
`access2Str64_satisfiable`, in `Janus.Contracts.MapStrSat`) uses the model `MS0`, in which every map is nil (a lookup returns
the zero value and `false`), with model code that returns a pointer to a zero slot.
-/

namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem

/-- The key of the string with data pointer `p` and length `n` in `m`: its length and its bytes
(as a little-endian number). -/
def strKey (m : Memory) (p n : Nat) : Nat × Nat := (n, m.readLE p n)

/-- Equal strings (Go's `==` on the headers at `a` and `b`) are the same key. -/
theorem strKey_eq_of_strEq {m : Memory} {a b : Nat} (h : strEq m a b = true) :
    strKey m (strPtr m a) (strLen m a) = strKey m (strPtr m b) (strLen m b) := by
  simp only [strEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [strKey]; rw [h2, h1]

/-- **`runtime.mapaccess2_faststr(t, m, key)`** (arm64: `X0 = t`, `X1 = m`, `X2`/`X3` the key's
data pointer and length) for a `map[string]V` with 8-byte values: as `Map.Access2`, for the key
`strKey` of the key's bytes, which must be readable and outside the callee's stack window. -/
def Access2Str (p : Program) (addr : Nat) (M : MapModel (Nat × Nat) (BitVec 64)) : Prop :=
  ∀ f, Summary p addr
    (fun s => Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
      (s.regs 2).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧
      s.mem.accessible (s.regs 2).toNat (s.regs 3).toNat false = true ∧
      Outside (s.regs 2).toNat (s.regs 3).toNat (calleeStack s M.depth 4))
    (fun s s' => Map.RTReturn M 4 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      Map.SlotHolds M m (r 0).toNat ((f (strKey s.mem (s.regs 2).toNat (s.regs 3).toNat)).getD 0) ∧
      (r 1).toNat % 256 = (f (strKey s.mem (s.regs 2).toNat (s.regs 3).toNat)).isSome.toNat)

end Janus.Contracts.MapStr

namespace Janus.Contracts.MapStr

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec.Map
open Janus (Outside)

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

end Janus.Contracts.MapStr
