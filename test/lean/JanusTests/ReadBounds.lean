import Janus

/-! # Read bounds in the omega-based dischargers (S12)

`omega` sees `m.readLE a n` as an unbounded natural. `janus_omega_staged` (the `Outside`/frame dischargers) and the
branch pruning (`janus_omega_prune`) add `m.readLE a n < 256^n` (`Memory.readLE_lt`) for the reads of their goal, so facts that hold only
because a read is a 64-bit (or smaller) value are provable. Each example below is false for an unbounded read. -/

namespace JanusTests.ReadBounds
open Janus Janus.Arm64

example (m : Memory) (p : Nat) : m.readLE p 8 < 2 ^ 64 := by janus_omega_staged

example (m : Memory) (p q : Nat) : m.readLE p 4 + m.readLE q 4 < 2 ^ 33 := by janus_omega_staged

/-- The limb comparison of `cmp`/`ja`: with `y ≤ x` the flag condition `(2^64 - x + y) % 2^64 = 0` is `y = x`. -/
example (m : Memory) (p q : Nat) (h : m.readLE p 8 ≤ m.readLE q 8) (hne : m.readLE p 8 ≠ m.readLE q 8) :
    (2 ^ 64 - m.readLE q 8 + m.readLE p 8) % 2 ^ 64 ≠ 0 := by janus_omega_staged

end JanusTests.ReadBounds
