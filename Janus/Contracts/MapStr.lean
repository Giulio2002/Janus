import Janus.Contracts.Hash
import Janus.Contracts.MapVar

/-!
# String-keyed map lookup (`runtime.mapaccess2_faststr`, arm64 and amd64)

A `map[string]V` keys its entries by the strings' contents: two strings with the same length
and bytes are the same key whatever their data pointers (Go's `==`, `Mem.strEq`). That is what
makes the runtime's lookup correct: it hashes the key with `strhash`, whose result depends only
on the length and the bytes (`Hash.Strhash`; equal strings hash alike,
`HashLaws.strhash_of_strEq`), and compares the candidates in the probed group with string
equality. So the abstract map of `Janus.Spec.Map` is keyed here by the content
`strKey m p n = (n, bytes)`, and `strKey_eq_of_strEq` turns Go's string equality into equality of
keys.

| Go | Runtime call (Go 1.26) | Contract |
| --- | --- | --- |
| `v := m[k]` | `runtime.mapaccess1_faststr(t, m, k) *V` | `Access1Str` |
| `v, ok := m[k]` | `runtime.mapaccess2_faststr(t, m, k) (*V, bool)` | `Access2Str` (8-byte values) |
| `m[k] = v` | `runtime.mapassign_faststr(t, m, k) *V` | `AssignStr` |
| `delete(m, k)` | `runtime.mapdelete_faststr(t, m, k)` | `DeleteStr` |

**The key's bytes after an assignment.** `mapassign_faststr` stores the key's header (pointer
and length) in the map, not a copy of its bytes, so the map's contents, keyed by those bytes,
depend on them from then on. `AssignStr` therefore requires them in the runtime's memory
(`StrOwned`: Go strings are immutable and live in the heap or in read-only data, which a model
counts as the runtime's), so that the representation stays inside `M.priv` (`MapModel.Laws`).

The contracts have the frame of `Janus.Contracts.Map` (`Map.RTPre`, `Map.RTReturn`); the amd64
ones are in `Janus.Contracts.MapStrAmd64`, the satisfiability witnesses in
`Janus.Contracts.MapStrSat` and `MapStrSatAmd64`.
-/

namespace Janus.Contracts.MapStr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Contracts
  Janus.Contracts.Mem Janus.Contracts.MapVar

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

/-- The key bytes `[p, p + n)` of a string stored in a map are the runtime's: empty, or inside
`M.priv` (see the module documentation). -/
def StrOwned {K V : Type} (M : MapModel K V) (p n : Nat) : Prop := n = 0 ∨ InRanges p n M.priv

/-- The string key `(X2, X3)` is readable, below `2^48` and outside the callee's stack window. -/
def StrIn (s : State) (d nargs : Nat) : Prop :=
  (s.regs 2).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧
    s.mem.accessible (s.regs 2).toNat (s.regs 3).toNat false = true ∧
    Outside (s.regs 2).toNat (s.regs 3).toNat (calleeStack s d nargs)

/-- **`runtime.mapaccess1_faststr(t, m, key)`** for a `map[string]V` with `vs`-byte values:
returns a pointer to the value of the key's content, or to a zero value. -/
def Access1Str (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
      StrIn s M.depth 4)
    (fun s s' => Map.RTReturn M 4 [] (s.regs 1).toNat s s' fun r m =>
      IsMap M m (s.regs 1).toNat f ∧
      SlotHoldsN M m (r 0).toNat vs ((f (strKey s.mem (s.regs 2).toNat (s.regs 3).toNat)).getD 0).toNat)

/-- **`runtime.mapassign_faststr(t, m, key)`** on a non-nil map, when the runtime is ready for
the call (`H` sees the key's header and bytes): returns the value slot of the key's content
(`Map.AssignSlot`). The key's bytes must be the runtime's (`StrOwned`). -/
def AssignStr (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs)))
    (H : RtReady) : Prop :=
  ∀ f, Summary p addr
    (fun s => Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ (s.regs 1).toNat ≠ 0 ∧
      M.Rep s.mem (s.regs 1).toNat f ∧ StrIn s M.depth 4 ∧
      StrOwned M (s.regs 2).toNat (s.regs 3).toNat ∧
      Ready H M.priv [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat, (s.regs 3).toNat] s)
    (fun s s' => Map.RTReturn M 4 [] (s.regs 1).toNat s s' fun r m =>
      Map.AssignSlot vs M (s.regs 1).toNat f (strKey s.mem (s.regs 2).toNat (s.regs 3).toNat)
        (s.regs 28) (r 0).toNat m)

/-- **`runtime.mapdelete_faststr(t, m, key)`**: removes the key's content (nothing happens for
a nil map or an absent key). -/
def DeleteStr (p : Program) (addr : Nat) (vs : Nat) (M : MapModel (Nat × Nat) (BitVec (8 * vs))) :
    Prop :=
  ∀ f, Summary p addr
    (fun s => Map.RTPre M 4 s ∧ M.Typ (s.regs 0).toNat ∧ IsMap M s.mem (s.regs 1).toNat f ∧
      StrIn s M.depth 4)
    (fun s s' => Map.RTReturn M 4 [] (s.regs 1).toNat s s' fun _ m =>
      IsMap M m (s.regs 1).toNat (f.erase (strKey s.mem (s.regs 2).toNat (s.regs 3).toNat)))

end Janus.Contracts.MapStr

