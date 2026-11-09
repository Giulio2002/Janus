import Janus

/-! # Where a string result lives (U-SBTS-POST)

`slicebytetostringSpec st` says, besides the bytes, where the result `(r0, n)` is (`StrAt`): nowhere (`n = 0`);
`&staticuint64s[b]` (`n = 1`, `r0 = st + 8 b`); the caller's `*tmpBuf` (`2 ≤ n ≤ 32`); a new block inside `rt`.
A consumer that calls a second runtime function on the result needs it outside that call's stack window; `StrAt.outside`
derives it from layout facts, one hypothesis per disjunct. -/

namespace JanusTests.StrAt
open Janus Janus.Arm64 Janus.Contracts Janus.Spec

/-- `n = 0`: nothing to be outside. -/
example (rt : List (Nat × Nat)) (buf st ptr r0 lo len : Nat) (m0 : Memory) (hrt : Outside lo len rt)
    (hbuf : buf = 0 ∨ buf + 32 ≤ lo ∨ lo + len ≤ buf) (hst : st + 2048 ≤ lo ∨ lo + len ≤ st)
    (h : StrAt rt buf st ptr 0 r0 m0) : 0 = 0 ∨ r0 + 0 ≤ lo ∨ lo + len ≤ r0 :=
  StrAt.outside h lo len hrt hbuf hst

/-- `n = 1`: `r0 = st + 8 b` with `b` a byte: inside the table, outside by the layout fact on `st`. -/
example (rt : List (Nat × Nat)) (buf st ptr lo len : Nat) (m0 : Memory) (hrt : Outside lo len rt)
    (hbuf : buf = 0 ∨ buf + 32 ≤ lo ∨ lo + len ≤ buf) (hst : st + 2048 ≤ lo ∨ lo + len ≤ st)
    (h : StrAt rt buf st ptr 1 (st + 8 * m0.readLE ptr 1) m0) :
    (st + 8 * m0.readLE ptr 1) + 1 ≤ lo ∨ lo + len ≤ st + 8 * m0.readLE ptr 1 := by
  rcases StrAt.outside h lo len hrt hbuf hst with h | h | h <;> omega

/-- The caller's buffer. -/
example (rt : List (Nat × Nat)) (buf st ptr n lo len : Nat) (m0 : Memory) (hrt : Outside lo len rt)
    (hbuf : buf + 32 ≤ lo) (hst : st + 2048 ≤ lo ∨ lo + len ≤ st) (hn : 2 ≤ n ∧ n ≤ 32) (hb : buf ≠ 0) :
    StrAt rt buf st ptr n buf m0 → buf + n ≤ lo ∨ lo + len ≤ buf := by
  intro h
  rcases StrAt.outside h lo len hrt (Or.inr (Or.inl hbuf)) hst with h | h | h <;> omega

/-- A block inside the runtime-owned ranges. -/
example (rt : List (Nat × Nat)) (buf st ptr n r0 lo len : Nat) (m0 : Memory) (hrt : Outside lo len rt)
    (hbuf : buf = 0 ∨ buf + 32 ≤ lo ∨ lo + len ≤ buf) (hst : st + 2048 ≤ lo ∨ lo + len ≤ st)
    (h : StrAt rt buf st ptr n r0 m0) (hi : InRanges r0 n rt) (hn : 2 ≤ n) :
    r0 + n ≤ lo ∨ lo + len ≤ r0 := by
  rcases StrAt.outside h lo len hrt hbuf hst with h | h | h <;> omega

/-- From the contract's postcondition itself. -/
example (st : Nat) (rt : List (Nat × Nat)) (a : List Nat) (m0 m : Memory) (r0 r1 r2 lo len : Nat)
    (hpost : (slicebytetostringSpec st).post rt a m0 r0 r1 r2 m) (hrt : Outside lo len rt)
    (hbuf : arg a 0 = 0 ∨ arg a 0 + 32 ≤ lo ∨ lo + len ≤ arg a 0) (hst : st + 2048 ≤ lo ∨ lo + len ≤ st) :
    r1 = 0 ∨ r0 + r1 ≤ lo ∨ lo + len ≤ r0 :=
  StrAt.outside hpost.2 lo len hrt hbuf hst

/-- A concatenation: an operand, the buffer, or a block of `rt`. -/
example (rt : List (Nat × Nat)) (buf r0 n lo len : Nat) (ops : List (Nat × Nat)) (hrt : Outside lo len rt)
    (hbuf : buf = 0 ∨ buf + 32 ≤ lo ∨ lo + len ≤ buf)
    (hops : ∀ x ∈ ops, x.2 = 0 ∨ x.1 + x.2 ≤ lo ∨ lo + len ≤ x.1) (h : CatStrAt rt buf ops r0 n) :
    n = 0 ∨ r0 + n ≤ lo ∨ lo + len ≤ r0 :=
  CatStrAt.outside h lo len hrt hbuf hops

/-- The live layer: a result is fresh only when it is a new block (`n ≥ 2`, no buffer), never the static table or an operand. -/
example (a : List Nat) (m : Memory) (r0 r1 r2 : Nat) (h : (slicebytetostringLive.fresh a m r0 r1 r2) ≠ []) :
    2 ≤ r1 ∧ (arg a 0 = 0 ∨ 32 < r1) := by
  by_cases hc : 2 ≤ r1 ∧ (arg a 0 = 0 ∨ 32 < r1)
  · exact hc
  · exact absurd (if_neg hc) h

end JanusTests.StrAt
