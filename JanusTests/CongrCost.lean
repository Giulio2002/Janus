import Janus

/-!
# `janus_congr` stays cheap on a borrow-chain write

The shape of a subtract-with-borrow loop's memory store: a word `r - 1` (the specification) against
`2^64 - 1 + r` (what `ADD x, x, #-1` computes), both written through `Memory.writeLE_mod`. Plain
`congr 1` closes its subgoals by `rfl` at default transparency and unfolds `Nat.sub`/`Nat.add` on
the `2^64` literal against the symbolic `readLE` term (445 to 500 s per call in a consumer's loop
theorem). `janus_congr` tries `with_reducible congr 1` first; this test fails (heartbeat limit) if
that stops being cheap. The limit is far below what the default-transparency attempt needs.
-/

namespace JanusTests.CongrCost
open Janus Janus.Arm64

set_option maxHeartbeats 200000 in
theorem borrow_word (m m' : Memory) (a p : Nat) (hne : m.readLE a 8 ≠ 0) :
    m'.writeLE p 8 (m.readLE a 8 - 1) = m'.writeLE p 8 (18446744073709551615 + m.readLE a 8) := by
  have hl := Memory.readLE_lt m a 8
  rw [← Memory.writeLE_mod (n := 8) (v := m.readLE a 8 - 1),
    ← Memory.writeLE_mod (n := 8) (v := 18446744073709551615 + m.readLE a 8)]
  janus_congr
  simp only [Nat.reducePow] at hl ⊢
  omega

end JanusTests.CongrCost
