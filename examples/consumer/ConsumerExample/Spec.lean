import Janus

/-!
# Shared specifications and lemmas

This module does not import `Extracted`, so it is independent of any extraction: `lake build`
builds it, and `janus verify` / `janus verify-batch` reuse its build across every extraction it
is verified against. Both theorem modules (`ConsumerExample.Add`, `ConsumerExample.Max`) import it.
-/

open Janus Janus.GoABI

namespace ConsumerExample

/-- `func Add(x, y uint64) uint64 { return x + y }`: wrapping 64-bit addition. -/
def addSpec (x y : BitVec 64) : BitVec 64 := x + y

/-- `func Max(x, y uint64) uint64`: the larger argument, unsigned. -/
def maxSpec (x y : BitVec 64) : BitVec 64 := if y.toNat < x.toNat then x else y

/-- The shape both theorems share: for all 64-bit `x` and `y`, a Go call of `entry` with `x`
in `X0` and `y` in `X1` (everything else arbitrary) returns, obeys the Go ABI, and leaves
`f x y` in `X0`. -/
def Computes (p : Program) (entry : Nat) (f : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ x y : BitVec 64, Ensures p entry [x, y] (fun _ => True) (fun _ s' => s'.regs 0 = f x y)

theorem addSpec_toNat (x y : BitVec 64) : (addSpec x y).toNat = (x.toNat + y.toNat) % 2 ^ 64 :=
  BitVec.toNat_add x y

theorem le_maxSpec_left (x y : BitVec 64) : x.toNat ≤ (maxSpec x y).toNat := by
  unfold maxSpec; split <;> omega

theorem le_maxSpec_right (x y : BitVec 64) : y.toNat ≤ (maxSpec x y).toNat := by
  unfold maxSpec; split <;> omega

end ConsumerExample
